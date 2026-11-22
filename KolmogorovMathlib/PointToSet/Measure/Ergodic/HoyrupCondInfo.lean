/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupBasic

/-!
# Conditional information along a sequence

For a shift-invariant probability measure `ν` on `ℕ → Bool`, the information of the first symbol
given the next `j` symbols,
`condInfo ν j x = -log₂ (ν[x₀ x₁ … x_j] / ν[x₁ … x_j])` (`= ⊤` when the ratio is `0`; note
`ν[x₀…x_j] ≤ ν[x₁…x_j]` by invariance), satisfies the telescoping identity of Hoyrup (STACS 2012,
(3)): `-log₂ ν[x↾n] = ∑_{k<n} condInfo ν (n-1-k) (σ^k x)`. Hence, for `n ≥ N`,
`-log₂ ν[x↾n] ≥ ∑_{k < n-N} min(g_N, L)(σ^k x)` with `g_N = ⨅_{j ≥ N} condInfo ν j`.

The truncation `min(g_N, L) = L - truncDefect ν N L`, where
`truncDefect ν N L = ⨆_{j ≥ N} (L - min(condInfo ν j, L))` is bounded by `L` and lower
semicomputable relative to any oracle computing `ν` (`{condInfo ν j < c}` is the union of the
cylinders `[w]`, `|w| = j + 1`, with `ν[w] > 2^{-c} ν[w₁…w_j]`). For a rational threshold `q`
and `q' = max(q, 0) < L`, the irrational factor `2^{q'-L}` is handled through rational witnesses
`r < ν[w]`, `ν[w₁…w_j] < s` with `2^{q'-L} s < r`, the last comparison being decided exactly in
natural-number arithmetic (raise both sides to the power `den q'`).

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- The conditional information `-log₂ ν[x₀ | x₁ … x_j]`, computed as
`infoBits (ν[x↾(j+1)] / ν[(σx)↾j])`. Blueprint node `erg:hoyrup`. -/
noncomputable def condInfo (ν : Measure (ℕ → Bool)) (j : ℕ) (x : ℕ → Bool) : ℝ≥0∞ :=
  infoBits (ν (listCylinder (wordPrefix x (j + 1))) /
    ν (listCylinder (wordPrefix (shiftMap x) j)))

/-- The truncation defect `⨆_{j ≥ N} (L - min(condInfo ν j, L))`. Blueprint node `erg:hoyrup`. -/
noncomputable def truncDefect (ν : Measure (ℕ → Bool)) (N L : ℕ) (x : ℕ → Bool) : ℝ≥0∞ :=
  ⨆ j ≥ N, ((L : ℝ≥0∞) - min (condInfo ν j x) L)

/-! ### Private helpers on cylinders and information -/

/-- A sequence in the cylinder `[w]` has `w` as its prefix of length `|w|`. -/
private lemma ci_wordPrefix_eq_of_mem {x : ℕ → Bool} {w : List Bool} (hx : x ∈ listCylinder w) :
    wordPrefix x w.length = w := by
  apply List.ext_getElem
  · simp [wordPrefix]
  · intro i h1 h2
    simp only [wordPrefix, List.getElem_ofFn]
    exact hx i h2

/-- Invariance on cylinders: `ν[a v] ≤ ν[v]`. -/
private lemma ci_measure_cons_le {ν : Measure (ℕ → Bool)} (hν : MeasurePreserving shiftMap ν ν)
    (a : Bool) (v : List Bool) : ν (listCylinder (a :: v)) ≤ ν (listCylinder v) := by
  have hsub : listCylinder (a :: v) ⊆ shiftMap ⁻¹' listCylinder v := by
    intro y hy i hi
    exact hy (i + 1) (by simpa using hi)
  calc ν (listCylinder (a :: v)) ≤ ν (shiftMap ⁻¹' listCylinder v) := measure_mono hsub
    _ = ν (listCylinder v) :=
      hν.measure_preimage (measurableSet_listCylinder v).nullMeasurableSet

/-- The information is additive along a chain of masses: for `0 < a ≤ b ≤ 1`,
`infoBits (a / b) + infoBits b = infoBits a`. -/
private lemma ci_infoBits_div_add {a b : ℝ≥0∞} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    infoBits (a / b) + infoBits b = infoBits a := by
  have hbt : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt hab
  have hb0 : b ≠ 0 := (ha.trans_le hab).ne'
  have hab0 : a / b ≠ 0 := ENNReal.div_ne_zero.2 ⟨ha.ne', hbt⟩
  have har : 0 < a.toReal := ENNReal.toReal_pos ha.ne' hat
  have hbr : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  have habr : a.toReal ≤ b.toReal := ENNReal.toReal_mono hbt hab
  have hb1 : b.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hb
  rw [infoBits_of_ne hab0, infoBits_of_ne hb0, infoBits_of_ne ha.ne', ENNReal.toReal_div,
    ← ENNReal.ofReal_add]
  · congr 1
    rw [Real.logb_div har.ne' hbr.ne']
    ring
  · have : a.toReal / b.toReal ≤ 1 := div_le_one_of_le₀ habr hbr.le
    have := Real.logb_nonpos one_lt_two (div_nonneg har.le hbr.le) this
    linarith
  · have := Real.logb_nonpos one_lt_two hbr.le hb1
    linarith

/-- The conditional information is a function of the prefix `x↾(j+1)`. -/
private lemma ci_condInfo_eq (ν : Measure (ℕ → Bool)) (j : ℕ) (x : ℕ → Bool) :
    condInfo ν j x = infoBits (ν (listCylinder (wordPrefix x (j + 1))) /
      ν (listCylinder (wordPrefix x (j + 1)).tail)) := by
  rw [condInfo, wordPrefix_succ, List.tail_cons]

/-! ### Private helpers for lower semicomputability -/

/-- For `0 ≤ q`: `q < L - min(c, L)` iff `q < L` and `c < L - q`. -/
private lemma ci_lt_sub_min_iff (L : ℕ) {q : ℝ} (hq : 0 ≤ q) (c : ℝ≥0∞) :
    ENNReal.ofReal q < (L : ℝ≥0∞) - min c L ↔ q < L ∧ c < ENNReal.ofReal (L - q) := by
  rcases lt_or_ge c L with hc | hc
  · have hct : c ≠ ⊤ := ne_top_of_lt hc
    have hγ : c.toReal < L := by
      simpa using ENNReal.toReal_strict_mono (ENNReal.natCast_ne_top L) hc
    have hγ0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    rw [min_eq_left hc.le, ← ENNReal.ofReal_toReal hct, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_sub _ hγ0, ENNReal.ofReal_lt_ofReal_iff', ENNReal.ofReal_lt_ofReal_iff']
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨-, h2, -⟩
      exact ⟨by linarith, by linarith⟩
  · rw [min_eq_right hc, tsub_self]
    simp only [ENNReal.not_lt_zero, false_iff, not_and, not_lt]
    intro _
    refine le_trans ?_ hc
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For `t > 0`: `infoBits r < t` iff `2^{-t} < r`. -/
private lemma ci_infoBits_lt_iff {t : ℝ} (ht : 0 < t) (r : ℝ≥0∞) :
    infoBits r < ENNReal.ofReal t ↔ ENNReal.ofReal ((2 : ℝ) ^ (-t)) < r := by
  rcases eq_or_ne r 0 with rfl | h0
  · simp
  rcases eq_or_ne r ⊤ with rfl | hrt
  · simp [ht]
  have hpos : 0 < r.toReal := ENNReal.toReal_pos h0 hrt
  rw [infoBits_of_ne h0, ENNReal.ofReal_lt_ofReal_iff ht,
    ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hrt,
    ← Real.lt_logb_iff_rpow_lt one_lt_two hpos]
  constructor <;> intro h <;> linarith

/-- For `k > 0` and finite masses: `k < a / b` iff `k b < a`. -/
private lemma ci_lt_div_iff {k : ℝ} (hk : 0 < k) {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ENNReal.ofReal k < a / b ↔ k * b.toReal < a.toReal := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by simpa using hk
  rw [ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.ofReal_ne_top) (Or.inl hb)]
  have : ENNReal.ofReal k * b = ENNReal.ofReal (k * b.toReal) := by
    rw [ENNReal.ofReal_mul hk.le, ENNReal.ofReal_toReal hb]
  rw [this, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ha]

/-- Rational witnesses for a strict inequality `k β < α`. -/
private lemma ci_exists_rat_iff {k α β : ℝ} (hk : 0 < k) (hβ : 0 ≤ β) :
    k * β < α ↔ ∃ r s : ℚ, 0 < r ∧ 0 < s ∧ k * s < r ∧ (r : ℝ) < α ∧ β < s := by
  constructor
  · intro h
    set ε := (α - k * β) / (2 * k) with hε_def
    have hε : 0 < ε := div_pos (by linarith) (by linarith)
    obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (lt_add_of_pos_right β hε)
    have hks : k * s < α := by
      have h1 : k * s < k * (β + ε) := mul_lt_mul_of_pos_left hs2 hk
      have h2 : k * (β + ε) = k * β + (α - k * β) / 2 := by
        rw [hε_def]
        field_simp
      linarith
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hks
    have hs0 : (0 : ℝ) < s := by linarith
    have hr0 : (0 : ℝ) < r := lt_trans (mul_pos hk hs0) hr1
    exact ⟨r, s, by exact_mod_cast hr0, by exact_mod_cast hs0, hr1, hr2, hs1⟩
  · rintro ⟨r, s, -, -, h1, h2, h3⟩
    nlinarith [mul_lt_mul_of_pos_left h3 hk]

/-- The cast of the numerator of a nonnegative rational. -/
private lemma ci_cast_num_toNat {q : ℚ} (hq : 0 ≤ q) :
    ((q.num.toNat : ℕ) : ℝ) = q * q.den := by
  have h : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
  rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num.toNat : ℤ) : ℝ) by norm_cast, h]
  exact_mod_cast (Rat.mul_den_eq_num q).symm

/-- The comparison `2^{q-L} s < r` (`q ≥ 0`, `r, s > 0` rational) in natural-number arithmetic. -/
private lemma ci_pow_iff {q : ℚ} (hq : 0 ≤ q) (L : ℕ) {r s : ℚ} (hr : 0 < r) (hs : 0 < s) :
    2 ^ q.num.toNat * (s.num.toNat * r.den) ^ q.den <
      2 ^ (L * q.den) * (r.num.toNat * s.den) ^ q.den ↔
    (2 : ℝ) ^ ((q : ℝ) - L) * s < r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  rw [← pow_lt_pow_iff_left₀ (a := (2 : ℝ) ^ ((q : ℝ) - L) * s) (b := (r : ℝ))
    (by positivity) hr'.le q.den_nz, mul_pow ((2 : ℝ) ^ ((q : ℝ) - L)) (s : ℝ),
    ← Real.rpow_mul_natCast (by norm_num)]
  have he : ((q : ℝ) - L) * q.den = ((q.num.toNat : ℕ) : ℝ) - ((L * q.den : ℕ) : ℝ) := by
    rw [ci_cast_num_toNat hq]
    push_cast
    ring
  rw [he, Real.rpow_sub two_pos, Real.rpow_natCast, Real.rpow_natCast, div_mul_eq_mul_div,
    div_lt_iff₀ (by positivity), ← Nat.cast_lt (α := ℝ)]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [ci_cast_num_toNat hs.le, ci_cast_num_toNat hr.le]
  have hP : (0 : ℝ) < ((s.den : ℝ) * r.den) ^ q.den := by positivity
  have e1 : (2 : ℝ) ^ q.num.toNat * ((s : ℝ) * s.den * r.den) ^ q.den =
      (2 ^ q.num.toNat * (s : ℝ) ^ q.den) * ((s.den : ℝ) * r.den) ^ q.den := by ring
  have e2 : (2 : ℝ) ^ (L * q.den) * ((r : ℝ) * r.den * s.den) ^ q.den =
      ((r : ℝ) ^ q.den * 2 ^ (L * q.den)) * ((s.den : ℝ) * r.den) ^ q.den := by ring
  rw [e1, e2]
  exact mul_lt_mul_iff_of_pos_right hP

/-- The per-word description of `{q < L - min(condInfo, L)}` by rational witnesses. -/
private lemma ci_key (ν : Measure (ℕ → Bool)) [IsFiniteMeasure ν] (L : ℕ) (q : ℚ)
    (w : List Bool) :
    ENNReal.ofReal q < (L : ℝ≥0∞) -
        min (infoBits (ν (listCylinder w) / ν (listCylinder w.tail))) L ↔
      max q 0 < (L : ℚ) ∧ ∃ r s : ℚ, 0 < r ∧ 0 < s ∧
        2 ^ (max q 0).num.toNat * (s.num.toNat * r.den) ^ (max q 0).den <
          2 ^ (L * (max q 0).den) * (r.num.toNat * s.den) ^ (max q 0).den ∧
        (r : ℝ) < (ν (listCylinder w)).toReal ∧ (ν (listCylinder w.tail)).toReal < s := by
  set q' := max q 0 with hq'_def
  have hq'0 : 0 ≤ q' := le_max_right _ _
  have hq'0' : (0 : ℝ) ≤ q' := by exact_mod_cast hq'0
  have hof : ENNReal.ofReal q = ENNReal.ofReal q' := by
    rcases le_total 0 q with h | h
    · rw [hq'_def, max_eq_left h]
    · rw [hq'_def, max_eq_right h, ENNReal.ofReal_of_nonpos (by exact_mod_cast h)]
      simp
  rw [hof, ci_lt_sub_min_iff L hq'0']
  have hcast : (q' : ℝ) < L ↔ q' < (L : ℚ) := by exact_mod_cast Iff.rfl
  rw [hcast]
  refine and_congr_right fun hqL ↦ ?_
  have ht : (0 : ℝ) < L - q' := by
    have : (q' : ℝ) < L := by exact_mod_cast hqL
    linarith
  have hk : (0 : ℝ) < 2 ^ ((q' : ℝ) - L) := by positivity
  rw [ci_infoBits_lt_iff ht, neg_sub,
    ci_lt_div_iff hk (measure_ne_top _ _) (measure_ne_top _ _),
    ci_exists_rat_iff hk ENNReal.toReal_nonneg]
  refine exists_congr fun r ↦ exists_congr fun s ↦ ?_
  constructor
  · rintro ⟨hr, hs, h1, h2, h3⟩
    exact ⟨hr, hs, (ci_pow_iff hq'0 L hr hs).2 h1, h2, h3⟩
  · rintro ⟨hr, hs, h1, h2, h3⟩
    exact ⟨hr, hs, (ci_pow_iff hq'0 L hr hs).1 h1, h2, h3⟩

/-! ### The theorems -/

/-- Each `condInfo ν j` is measurable. Blueprint node `erg:hoyrup`. -/
theorem measurable_condInfo (ν : Measure (ℕ → Bool)) (j : ℕ) : Measurable (condInfo ν j) := by
  have h : condInfo ν j = (fun v : Fin (j + 1) → Bool ↦ infoBits (ν (listCylinder (List.ofFn v)) /
      ν (listCylinder (List.ofFn v).tail))) ∘ (fun x i ↦ x i) := by
    funext x
    rw [ci_condInfo_eq]
    rfl
  rw [h]
  exact (measurable_of_finite _).comp (measurable_pi_iff.2 fun i ↦ measurable_pi_apply _)

/-- The telescoping identity: `-log₂ ν[x↾n] = ∑_{k<n} condInfo ν (n-1-k) (σ^k x)` when
`ν[x↾n] > 0`. Blueprint node `erg:hoyrup`. -/
theorem infoBits_cylinder_eq_sum_condInfo {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) {x : ℕ → Bool} {n : ℕ}
    (hpos : 0 < ν (listCylinder (wordPrefix x n))) :
    infoBits (ν (listCylinder (wordPrefix x n))) =
      ∑ k ∈ Finset.range n, condInfo ν (n - 1 - k) (shiftMap^[k] x) := by
  induction n generalizing x with
  | zero =>
    have h : listCylinder (wordPrefix x 0) = univ := by
      ext y
      simp [listCylinder, wordPrefix]
    rw [h, measure_univ, infoBits_of_ne one_ne_zero]
    simp
  | succ n ih =>
    have hle : ν (listCylinder (wordPrefix x (n + 1))) ≤
        ν (listCylinder (wordPrefix (shiftMap x) n)) := by
      rw [wordPrefix_succ]
      exact ci_measure_cons_le hν _ _
    rw [Finset.sum_range_succ', ← ci_infoBits_div_add hpos hle prob_le_one,
      ih (hpos.trans_le hle), add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Function.iterate_succ_apply]
    congr 1
    omega

/-- The lower bound used for Hoyrup's theorem:
`∑_{k < n-N} min(⨅_{j≥N} condInfo ν j, L)(σ^k x) ≤ -log₂ ν[x↾n]` for every `x`.
Blueprint node `erg:hoyrup`. -/
theorem sum_min_iInf_condInfo_le_infoBits {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving shiftMap ν ν) (x : ℕ → Bool) (N L n : ℕ) :
    ∑ k ∈ Finset.range (n - N), min (⨅ j ≥ N, condInfo ν j (shiftMap^[k] x)) (L : ℝ≥0∞) ≤
      infoBits (ν (listCylinder (wordPrefix x n))) := by
  rcases eq_or_ne (ν (listCylinder (wordPrefix x n))) 0 with h0 | h0
  · rw [h0, infoBits_zero]
    exact le_top
  rw [infoBits_cylinder_eq_sum_condInfo hν (pos_iff_ne_zero.2 h0)]
  calc ∑ k ∈ Finset.range (n - N), min (⨅ j ≥ N, condInfo ν j (shiftMap^[k] x)) (L : ℝ≥0∞)
      ≤ ∑ k ∈ Finset.range (n - N), condInfo ν (n - 1 - k) (shiftMap^[k] x) := by
        refine Finset.sum_le_sum fun k hk ↦ (min_le_left _ _).trans (iInf₂_le _ ?_)
        rw [Finset.mem_range] at hk
        omega
    _ ≤ ∑ k ∈ Finset.range n, condInfo ν (n - 1 - k) (shiftMap^[k] x) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le _ _))

/-- `min(⨅_{j≥N} condInfo ν j, L) + truncDefect ν N L = L`. Blueprint node `erg:hoyrup`. -/
theorem min_iInf_condInfo_add_truncDefect (ν : Measure (ℕ → Bool)) (N L : ℕ)
    (x : ℕ → Bool) :
    min (⨅ j ≥ N, condInfo ν j x) (L : ℝ≥0∞) + truncDefect ν N L x = L := by
  have hm : ∀ a : ℝ≥0∞, (L : ℝ≥0∞) - min a L = L - a := fun a ↦ by
    rcases le_total a L with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, tsub_self, tsub_eq_zero_of_le h]
  have key : truncDefect ν N L x = L - min (⨅ j ≥ N, condInfo ν j x) L := by
    simp only [truncDefect, hm, ENNReal.sub_iInf]
  rw [key]
  exact add_tsub_cancel_of_le (min_le_right _ _)

/-- The truncation defect is at most `L`. Blueprint node `erg:hoyrup`. -/
theorem truncDefect_le (ν : Measure (ℕ → Bool)) (N L : ℕ) (x : ℕ → Bool) :
    truncDefect ν N L x ≤ L :=
  iSup₂_le fun _ _ ↦ tsub_le_self

/-- The truncation defect is lower semicomputable relative to an oracle computing `ν` on
cylinders. (The invariance hypothesis is not needed by the proof; it is kept for the callers.)
Blueprint node `erg:hoyrup`. -/
theorem isLscFunIn_truncDefect {A : Set ℕ} {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (_hν : MeasurePreserving shiftMap ν ν) (hc : IsComputableWordMeasureIn A ν) (N L : ℕ) :
    IsLscFunIn A (truncDefect ν N L) := by
  classical
  let D : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) → Prop := fun z ↦
    max z.1.1.2 0 < (L : ℚ) ∧ N + 1 ≤ z.1.2.length ∧ 0 < z.2.1 ∧ 0 < z.2.2 ∧
      2 ^ (max z.1.1.2 0).num.toNat * (z.2.2.num.toNat * z.2.1.den) ^ (max z.1.1.2 0).den <
        2 ^ (L * (max z.1.1.2 0).den) * (z.2.1.num.toNat * z.2.2.den) ^ (max z.1.1.2 0).den
  have hD : PrimrecPred D := by
    have hm : Primrec fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦ max z.1.1.2 (0 : ℚ) :=
      ComputableReals.primrec_ratMax.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const 0)
    have hr : Primrec fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦ z.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hs : Primrec fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦ z.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hnum : Primrec fun x : ℚ ↦ x.num.toNat :=
      ComputableReals.primrec_intToNat.comp ComputableReals.primrec_ratNum
    have hden := ComputableReals.primrec_ratDen
    have hpow : Primrec₂ fun a b : ℕ ↦ a ^ b := Primrec.nat_iff.mpr Nat.Primrec.pow
    have hlhs : Primrec fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦
        2 ^ (max z.1.1.2 0).num.toNat * (z.2.2.num.toNat * z.2.1.den) ^ (max z.1.1.2 0).den :=
      Primrec.nat_mul.comp (hpow.comp (Primrec.const 2) (hnum.comp hm))
        (hpow.comp (Primrec.nat_mul.comp (hnum.comp hs) (hden.comp hr)) (hden.comp hm))
    have hrhs : Primrec fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦
        2 ^ (L * (max z.1.1.2 0).den) * (z.2.1.num.toNat * z.2.2.den) ^ (max z.1.1.2 0).den :=
      Primrec.nat_mul.comp
        (hpow.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const L) (hden.comp hm)))
        (hpow.comp (Primrec.nat_mul.comp (hnum.comp hr) (hden.comp hs)) (hden.comp hm))
    exact (ComputableReals.primrec_ratLt.comp hm (Primrec.const (L : ℚ))).and
      ((Primrec.nat_le.comp (Primrec.const (N + 1))
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))).and
      ((ComputableReals.primrec_ratLt.comp (Primrec.const 0) hr).and
      ((ComputableReals.primrec_ratLt.comp (Primrec.const 0) hs).and
      (Primrec.nat_lt.comp hlhs hrhs))))
  let F : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) → Prop := fun z ↦
    D z ∧ (z.2.1 : ℝ) < (ν (listCylinder z.1.2)).toReal ∧
      (ν (listCylinder z.1.2.tail)).toReal < z.2.2
  have hF : IsREIn A F := by
    have h1 : ComputableIn {charOracle A}
        fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦ (z.1.2, z.2.1) :=
      ((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).to_comp.computableIn
    have h2 : ComputableIn {charOracle A}
        fun z : ((Unit × ℚ) × List Bool) × (ℚ × ℚ) ↦ (z.1.2.tail, z.2.2) :=
      ((Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst)).pair
        (Primrec.snd.comp Primrec.snd)).to_comp.computableIn
    exact (isREIn_of_computable_decide hD.decide.to_comp).and
      (((birkhoff_computableIn_gt A _ hc).comp h1).and ((birkhoff_computableIn_lt A _ hc).comp h2))
  refine ⟨fun p ↦ ∃ y, F (p, y), hF.exists, fun _ q ↦ ?_⟩
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop, truncDefect, lt_iSup_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [ci_condInfo_eq, ci_key] at h
    obtain ⟨hqL, r, s, hr, hs, hp, h1, h2⟩ := h
    refine ⟨wordPrefix x (j + 1), ⟨(r, s), ⟨hqL, ?_, hr, hs, hp⟩, h1, h2⟩,
      mem_listCylinder_wordPrefix x _⟩
    simp only [wordPrefix, List.length_ofFn]
    omega
  · rintro ⟨w, ⟨⟨r, s⟩, ⟨hqL, hlen, hr, hs, hp⟩, h1, h2⟩, hx⟩
    dsimp only at hqL hlen hr hs hp h1 h2
    have hw := ci_wordPrefix_eq_of_mem hx
    refine ⟨w.length - 1, by omega, ?_⟩
    rw [ci_condInfo_eq, Nat.sub_add_cancel (by omega), hw, ci_key]
    exact ⟨hqL, r, s, hr, hs, hp, h1, h2⟩

end Kolmogorov.PointToSet
