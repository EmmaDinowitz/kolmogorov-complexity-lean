/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Computable
import KolmogorovMathlib.Oracle.KraftChaitin
import KolmogorovMathlib.AlgorithmicRandomness.NatLogPrimrec

/-!
# Coding by measure (Lemma 3.1)

Let `A` be admissible for `(X, d, T, μ)` with `μ(X) ≤ 1`. For each rational `ε > 0` there is a
constant `c` such that for every point `x` and every `n ≥ 1` with `μ(B_n(x, T, ε)) > 0`,
writing `I = -log₂ μ(B_n(x, T, ε))`,

`K_n^A(x, T, 6ε) ≤ I + 2 log₂ n + 2 log₂ (I + 2) + c`

(E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random points*,
Lemma 3.1). The sets `C_{n,k} = {i : μ(B_n(x_i, T, 2ε)) > 2^{-k}}` are `A`-c.e. uniformly; a
greedy `A`-c.e. subset `L_{n,k}` has members pairwise more than `4ε` apart in `d_n`, so it has
fewer than `2^k` members, and every member of `C_{n,k}` is within `5ε` of one of them. The
coding theorem for the weights `2^{-k} n^{-2} (k+1)^{-2}` bounds the complexity of the members
of `L_{n,k}`.

* `coding_by_measure`: the bound in the form used for limits, with any `k` such that
  `2^{-k} < μ(B_n(x, T, ε))` in place of `I + 1`.
* `coding_by_measure_info`: the bound as printed, in terms of `I`.

Only two properties of the measure are used: its total mass is at most one and the measures of
Bowen balls about ideal points are lower semicomputable in `A`.

Implementation: `greedyList` runs the greedy selection along an `A`-computable enumeration of
the triples `(n, k, i)` with `i ∈ C_{n,k}`, using a total `A`-computable test
(`exists_dec_far_near`) that separates Bowen distances `> 4ε` from `< 5ε`;
`card_le_two_pow_of_far` counts the selected centres of a slice by disjointness of their Bowen
balls; `exists_selection` collects the properties of the selection, and
`exists_complexity_le_selCost` applies the coding theorem with the natural-number cost
`selCost n k = k + 2 (⌊log₂ n⌋ + 1) + 2 (⌊log₂ (k + 1)⌋ + 1)`.

Blueprint node `meas:coding`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Greedy selection along an enumeration

An optional enumeration `e` of triples `(n, k, i)` is scanned stage by stage; a candidate is
kept when the test `dec` declares it far from every previously kept triple of the same slice
`(n, k)`. The kept triples form the list `greedyList e dec t` after `t` stages. -/

/-- A candidate `w = (n, k, i)` is compatible with a kept triple `v` when `v` lies in another
slice `(n', k')`, or when the test `dec` declares `i` far from the index of `v` at order `n`. -/
def greedyCompat (dec : ℕ × ℕ × ℕ → Bool) (w v : ℕ × ℕ × ℕ) : Bool :=
  !decide ((v.1, v.2.1) = (w.1, w.2.1)) || dec (w.1, w.2.2, v.2.2)

/-- A candidate is accepted by a list when it is compatible with every entry; the test is
written as a loop over the positions of the list. -/
def greedyAccepts (dec : ℕ × ℕ × ℕ → Bool) (w : ℕ × ℕ × ℕ) (L : List (ℕ × ℕ × ℕ)) : Bool :=
  (List.range L.length).all fun j ↦ greedyCompat dec w (L.getD j (0, 0, 0))

/-- Stage `t` enumerates a candidate accepted by the list `L`. -/
def greedyOk (e : ℕ → Option (ℕ × ℕ × ℕ)) (dec : ℕ × ℕ × ℕ → Bool) (t : ℕ)
    (L : List (ℕ × ℕ × ℕ)) : Bool :=
  (e t).isSome && greedyAccepts dec ((e t).getD (0, 0, 0)) L

/-- The list of triples kept after `t` stages of the greedy selection. -/
def greedyList (e : ℕ → Option (ℕ × ℕ × ℕ)) (dec : ℕ × ℕ × ℕ → Bool) :
    ℕ → List (ℕ × ℕ × ℕ)
  | 0 => []
  | t + 1 => cond (greedyOk e dec t (greedyList e dec t))
      ((e t).getD (0, 0, 0) :: greedyList e dec t) (greedyList e dec t)

/-- The stage-`t` output of the greedy selection: the candidate kept at stage `t`, if any. -/
def greedyEnum (e : ℕ → Option (ℕ × ℕ × ℕ)) (dec : ℕ × ℕ × ℕ → Bool) (t : ℕ) :
    Option (ℕ × ℕ × ℕ) :=
  cond (greedyOk e dec t (greedyList e dec t)) (e t) none

section Greedy

variable (e : ℕ → Option (ℕ × ℕ × ℕ)) (dec : ℕ × ℕ × ℕ → Bool)

/-- Acceptance means compatibility with every entry of the list. -/
lemma greedyAccepts_eq_true {w : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} :
    greedyAccepts dec w L = true ↔ ∀ v ∈ L, greedyCompat dec w v = true := by
  simp only [greedyAccepts, List.all_eq_true, List.mem_range]
  constructor
  · intro h v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have := h j hj
    rwa [List.getD_eq_getElem _ _ hj] at this
  · intro h j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem hj)

/-- A stage is accepted exactly when it enumerates an accepted candidate. -/
lemma greedyOk_eq_true {t : ℕ} {L : List (ℕ × ℕ × ℕ)} :
    greedyOk e dec t L = true ↔ ∃ w, e t = some w ∧ greedyAccepts dec w L = true := by
  cases h : e t <;> simp [greedyOk, h]

/-- Membership in the list after one more stage. -/
lemma mem_greedyList_succ {t : ℕ} {v : ℕ × ℕ × ℕ} :
    v ∈ greedyList e dec (t + 1) ↔ v ∈ greedyList e dec t ∨
      (greedyOk e dec t (greedyList e dec t) = true ∧ e t = some v) := by
  simp only [greedyList]
  cases hok : greedyOk e dec t (greedyList e dec t)
  · simp
  · obtain ⟨w, hw, -⟩ := (greedyOk_eq_true e dec).mp hok
    simp [hw, eq_comm, or_comm]

/-- The greedy lists grow with the stage. -/
lemma greedyList_mono {s t : ℕ} (hst : s ≤ t) {v : ℕ × ℕ × ℕ}
    (hv : v ∈ greedyList e dec s) : v ∈ greedyList e dec t := by
  induction t, hst using Nat.le_induction with
  | base => exact hv
  | succ t _ ih => exact (mem_greedyList_succ e dec).mpr (Or.inl ih)

/-- A triple is eventually kept exactly when it is output by the greedy enumeration. -/
lemma exists_mem_greedyList_iff (v : ℕ × ℕ × ℕ) :
    (∃ t, v ∈ greedyList e dec t) ↔ ∃ t, greedyEnum e dec t = some v := by
  constructor
  · rintro ⟨t, ht⟩
    induction t with
    | zero => simp [greedyList] at ht
    | succ t ih =>
      rcases (mem_greedyList_succ e dec).mp ht with h | ⟨hok, hv⟩
      · exact ih h
      · exact ⟨t, by simp [greedyEnum, hok, hv]⟩
  · rintro ⟨t, ht⟩
    cases hok : greedyOk e dec t (greedyList e dec t)
    · simp [greedyEnum, hok] at ht
    · simp only [greedyEnum, hok, Bool.cond_true] at ht
      exact ⟨t + 1, (mem_greedyList_succ e dec).mpr (Or.inr ⟨hok, ht⟩)⟩

/-- Every kept triple was enumerated. -/
lemma exists_eq_some_of_mem_greedyList {t : ℕ} {v : ℕ × ℕ × ℕ}
    (hv : v ∈ greedyList e dec t) : ∃ s, e s = some v := by
  obtain ⟨s, hs⟩ := (exists_mem_greedyList_iff e dec v).mp ⟨t, hv⟩
  cases hok : greedyOk e dec s (greedyList e dec s)
  · simp [greedyEnum, hok] at hs
  · simp only [greedyEnum, hok, Bool.cond_true] at hs
    exact ⟨s, hs⟩

/-- Every enumerated candidate is either kept or rejected because of a kept triple of the same
slice that the test does not declare far. -/
lemma exists_mem_greedyList_of_eq_some {t : ℕ} {w : ℕ × ℕ × ℕ} (hw : e t = some w) :
    ∃ v ∈ greedyList e dec (t + 1), v.1 = w.1 ∧ v.2.1 = w.2.1 ∧
      (v = w ∨ dec (w.1, w.2.2, v.2.2) = false) := by
  cases hok : greedyOk e dec t (greedyList e dec t)
  · have hacc : greedyAccepts dec w (greedyList e dec t) = false := by
      simpa [greedyOk, hw] using hok
    have hnot : ¬ ∀ v ∈ greedyList e dec t, greedyCompat dec w v = true := by
      rw [← greedyAccepts_eq_true]
      simp [hacc]
    simp only [not_forall, exists_prop] at hnot
    obtain ⟨v, hv, hcompat⟩ := hnot
    simp only [greedyCompat, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      not_or, Decidable.not_not, Prod.mk.injEq, Bool.not_eq_true] at hcompat
    exact ⟨v, (mem_greedyList_succ e dec).mpr (Or.inl hv), hcompat.1.1, hcompat.1.2,
      Or.inr hcompat.2⟩
  · exact ⟨w, (mem_greedyList_succ e dec).mpr (Or.inr ⟨hok, hw⟩), rfl, rfl, Or.inl rfl⟩

/-- Two kept triples of the same slice with different indices are declared far by the test,
for any symmetric relation `R` implied by a positive test. -/
lemma greedyList_pairwise (R : ℕ → ℕ → ℕ → Prop) (hR : ∀ n i j, R n i j → R n j i)
    (hdec : ∀ n i j, dec (n, i, j) = true → R n i j) (t : ℕ) :
    ∀ v ∈ greedyList e dec t, ∀ v' ∈ greedyList e dec t, v.1 = v'.1 → v.2.1 = v'.2.1 →
      v.2.2 ≠ v'.2.2 → R v.1 v.2.2 v'.2.2 := by
  induction t with
  | zero => simp [greedyList]
  | succ t ih =>
    cases hok : greedyOk e dec t (greedyList e dec t)
    · simpa only [greedyList, hok, Bool.cond_false] using ih
    · obtain ⟨w, hw, hacc⟩ := (greedyOk_eq_true e dec).mp hok
      have hcompat := (greedyAccepts_eq_true dec).mp hacc
      have hfar : ∀ v ∈ greedyList e dec t, v.1 = w.1 → v.2.1 = w.2.1 →
          R w.1 w.2.2 v.2.2 := by
        intro v hv h1 h2
        have hc := hcompat v hv
        simp only [greedyCompat, h1, h2, decide_true, Bool.not_true, Bool.false_or] at hc
        exact hdec _ _ _ hc
      simp only [greedyList, hok, hw, Option.getD_some, Bool.cond_true, List.mem_cons]
      rintro v (rfl | hv) v' (rfl | hv') h1 h2 h3
      · exact absurd rfl h3
      · exact hfar v' hv' h1.symm h2.symm
      · rw [h1]
        exact hR _ _ _ (hfar v hv h1 h2)
      · exact ih v hv v' hv' h1 h2 h3

/-- The acceptance test is computable relative to any oracle computing the test. -/
lemma computableIn_greedyAccepts {O : Set (ℕ →. ℕ)} (hdec : ComputableIn O dec) :
    ComputableIn O fun q : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) ↦ greedyAccepts dec q.1 q.2 := by
  have hslice : Primrec fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) ↦
      !decide ((p.2.1, p.2.2.1) = (p.1.1, p.1.2.1)) :=
    Primrec.not.comp (primrec_decideEq.comp
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  have hargs : Primrec fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) ↦ (p.1.1, p.1.2.2, p.2.2.2) :=
    (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hcompat : ComputableIn O fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) ↦
      greedyCompat dec p.1 p.2 := by
    have h := Primrec.or.computableIn.comp (O := O)
      (hslice.computableIn.pair (hdec.comp hargs.computableIn))
    exact h.of_eq fun p ↦ rfl
  have hget : Primrec fun r : ((ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)) × (ℕ × Bool) ↦
      r.1.2.getD r.2.1 (0, 0, 0) :=
    (Primrec.list_getD (0, 0, 0)).comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hstep : ComputableIn₂ O fun (q : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)) (p : ℕ × Bool) ↦
      p.2 && greedyCompat dec q.1 (q.2.getD p.1 (0, 0, 0)) := by
    have h := Primrec.and.computableIn.comp (O := O)
      ((Primrec.snd.comp Primrec.snd).computableIn.pair
        (hcompat.comp ((Primrec.fst.comp Primrec.fst).computableIn.pair hget.computableIn)))
    exact h.of_eq fun r ↦ rfl
  have hrec := ComputableIn.nat_rec (O := O)
    (f := fun q : (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) ↦ q.2.length)
    (Primrec.list_length.comp Primrec.snd).computableIn (ComputableIn.const true) hstep
  refine hrec.of_eq fun q ↦ ?_
  have key : ∀ m, @Nat.rec (fun _ ↦ Bool) true
      (fun y ih ↦ ih && greedyCompat dec q.1 (q.2.getD y (0, 0, 0))) m =
      (List.range m).all fun j ↦ greedyCompat dec q.1 (q.2.getD j (0, 0, 0)) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.all_append, ← ih, List.all_cons, List.all_nil, Bool.and_true]
  exact key _

/-- The greedy lists are computable relative to any oracle computing the enumeration and the
test. -/
lemma computableIn_greedyList {O : Set (ℕ →. ℕ)} (he : ComputableIn O e)
    (hdec : ComputableIn O dec) :
    ComputableIn O (greedyList e dec) ∧
      ComputableIn O fun t ↦ greedyOk e dec t (greedyList e dec t) := by
  have hacc := computableIn_greedyAccepts dec hdec
  have hget : ComputableIn O fun q : ℕ × List (ℕ × ℕ × ℕ) ↦ (e q.1).getD (0, 0, 0) :=
    (Primrec.option_getD.comp Primrec.id (Primrec.const (0, 0, 0))).computableIn.comp
      (he.comp ComputableIn.fst)
  have hok : ComputableIn O fun q : ℕ × List (ℕ × ℕ × ℕ) ↦ greedyOk e dec q.1 q.2 := by
    have h := Primrec.and.computableIn.comp (O := O) ((Primrec.option_isSome.computableIn.comp
      (he.comp ComputableIn.fst)).pair (hacc.comp (hget.pair ComputableIn.snd)))
    exact h.of_eq fun q ↦ rfl
  have hcons : ComputableIn O fun q : ℕ × List (ℕ × ℕ × ℕ) ↦ (e q.1).getD (0, 0, 0) :: q.2 := by
    have h := Primrec.list_cons.computableIn.comp (O := O) (hget.pair ComputableIn.snd)
    exact h.of_eq fun q ↦ rfl
  have hstep : ComputableIn₂ O fun (_ : ℕ) (q : ℕ × List (ℕ × ℕ × ℕ)) ↦
      cond (greedyOk e dec q.1 q.2) ((e q.1).getD (0, 0, 0) :: q.2) q.2 :=
    computable_in_cond (hok.comp ComputableIn.snd) (hcons.comp ComputableIn.snd)
      (ComputableIn.snd.comp ComputableIn.snd)
  have hrec := ComputableIn.nat_rec (O := O) (f := fun t : ℕ ↦ t) ComputableIn.id
    (ComputableIn.const ([] : List (ℕ × ℕ × ℕ))) hstep
  have hG : ComputableIn O (greedyList e dec) := by
    refine hrec.of_eq fun t ↦ ?_
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [greedyList] at ih ⊢
      rw [← ih]
  exact ⟨hG, hok.comp (ComputableIn.id.pair hG)⟩

end Greedy

/-! ### The decision procedure -/

/-- A relatively computable real family is separated at the thresholds `4ε` and `5ε` by a
total relatively computable test: a positive answer guarantees a value above `4ε`, a negative
one a value below `5ε`. -/
lemma exists_dec_far_near {A : Set ℕ} {D : ℕ × ℕ × ℕ → ℝ} (hD : IsComputableRealFamilyIn A D)
    {ε : ℚ} (hε : 0 < ε) :
    ∃ dec : ℕ × ℕ × ℕ → Bool, ComputableIn {charOracle A} dec ∧
      ∀ w, (dec w = true → 4 * (ε : ℝ) < D w) ∧ (dec w = false → D w < 5 * (ε : ℝ)) := by
  obtain ⟨q, hq, hqerr⟩ := hD
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨p, hp⟩ := exists_pow_lt_of_lt_one (half_pos hε') (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨fun w ↦ decide (9 / 2 * ε < q (w, p)), ?_, fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · have h := (Computable₂.computableIn₂ (O := {charOracle A}) computable₂_ratLt).comp
      (ComputableIn.const (9 / 2 * ε)) (hq.comp (ComputableIn.id.pair (ComputableIn.const p)))
    exact h.of_eq fun w ↦ rfl
  · have h' : ((9 / 2 * ε : ℚ) : ℝ) < q (w, p) := Rat.cast_lt.mpr (of_decide_eq_true h)
    push_cast at h'
    have := (abs_lt.mp (hqerr w p)).2
    linarith
  · have h' : ((q (w, p) : ℚ) : ℝ) ≤ ((9 / 2 * ε : ℚ) : ℝ) :=
      Rat.cast_le.mpr (not_lt.mp (of_decide_eq_false h))
    push_cast at h'
    have := (abs_lt.mp (hqerr w p)).1
    linarith

/-! ### Bowen balls and orbit complexity -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- The Bowen distance of a point to itself vanishes. -/
lemma bowenDist_self_eq_zero (T : X → X) (n : ℕ) (x : X) : bowenDist T n x x = 0 := by
  simp [bowenDist]

omit [MeasurableSpace X] [BorelSpace X] in
/-- An ideal point in the Bowen ball bounds the orbit complexity by its own complexity. -/
lemma orbitComplexityNat_le_of_mem (P : Presentation X) (T : X → X) (A : Set ℕ) {x : X}
    {n : ℕ} {r : ℝ} {j : ℕ} (hj : P.ι j ∈ bowenBall T n x r) :
    orbitComplexityNat P T A x n r ≤ oracleNatComplexity A j := by
  have h : orbitComplexity P T A x n r ≤ (oracleNatComplexity A j : ENat) := iInf₂_le j hj
  simpa [orbitComplexityNat] using ENat.toNat_le_toNat h (ENat.natCast_ne_top _)

/-! ### Counting -/

/-- Points pairwise at Bowen distance at least `2r` whose Bowen balls of radius `r` all have
measure above `2^{-k}` are at most `2^k` in number, for a measure of total mass at most one. -/
lemma card_le_two_pow_of_far (T : X → X) (hT : Continuous T) (μ : Measure X)
    (hμ : μ univ ≤ 1) {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (k : ℕ) (x : ℕ → X) (s : Finset ℕ)
    (hmass : ∀ j ∈ s, (2 : ℝ≥0∞)⁻¹ ^ k < μ (bowenBall T n (x j) r))
    (hfar : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → 2 * r ≤ bowenDist T n (x j) (x j')) :
    s.card ≤ 2 ^ k := by
  have hdisj : (s : Set ℕ).PairwiseDisjoint fun j ↦ bowenBall T n (x j) r := by
    intro j hj j' hj' hne
    refine Set.disjoint_left.mpr fun y hy hy' ↦ ?_
    rw [bowen_ball_dense_iff T n hn] at hy hy'
    have htri := bowen_ball_dense_triangle T n (x j) y (x j')
    rw [bowen_dist_comm T n y (x j')] at htri
    have := hfar j hj j' hj' hne
    linarith
  have hsum : ∑ j ∈ s, μ (bowenBall T n (x j) r) ≤ 1 := by
    rw [← measure_biUnion_finset hdisj fun j _ ↦
      (bowen_ball_dense_open T hT n (x j) r).measurableSet]
    exact (measure_mono (subset_univ _)).trans hμ
  have hle : (s.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ k ≤ 1 := by
    calc (s.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ k = ∑ _j ∈ s, (2 : ℝ≥0∞)⁻¹ ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ s, μ (bowenBall T n (x j) r) := Finset.sum_le_sum fun j hj ↦ (hmass j hj).le
      _ ≤ 1 := hsum
  have h2 : (s.card : ℝ≥0∞) ≤ 2 ^ k := by
    have := ENNReal.le_inv_iff_mul_le.mpr hle
    rwa [ENNReal.inv_pow, inv_inv] at this
  exact_mod_cast h2

/-! ### The selected centres -/

/-- The greedy selection: an `A`-enumerable set of triples `(n, k, j)` with at most `2^k`
members in each slice `(n, k)`, such that every point whose Bowen ball of radius `ε` has
measure above `2^{-k}` is within `6ε` of a selected ideal point of the slice `(n, k)`. -/
lemma exists_selection (P : Presentation X) (T : X → X) (hT : Continuous T) (A : Set ℕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1) (hA : IsMeasureAdmissible P T μ A)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ S : ℕ × ℕ × ℕ → Prop, IsREIn A S ∧
      (∀ (n k : ℕ) (s : Finset ℕ), (∀ j ∈ s, S (n, k, j)) → s.card ≤ 2 ^ k) ∧
      ∀ (x : X) (n k : ℕ), 1 ≤ n → (2 : ℝ≥0∞)⁻¹ ^ k < μ (bowenBall T n x (ε : ℝ)) →
        ∃ j, S (n, k, j) ∧ P.ι j ∈ bowenBall T n x (6 * (ε : ℝ)) := by
  classical
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  -- the candidates `C(n, k)`
  let C : ℕ × ℕ × ℕ → Prop := fun w ↦ 1 ≤ w.1 ∧
    (2 : ℝ≥0∞)⁻¹ ^ w.2.1 < μ (bowenBall T w.1 (P.ι w.2.2) ((2 * ε : ℚ) : ℝ))
  have hC : IsREIn A C := by
    have h1 : IsREIn A fun w : ℕ × ℕ × ℕ ↦ 1 ≤ w.1 :=
      isREIn_of_computable_decide
        (Primrec.nat_le.decide.comp (Primrec.const 1) Primrec.fst).to_comp
    have hmap : Computable fun w : ℕ × ℕ × ℕ ↦
        ((w.1, w.2.2, 2 * ε), ((2 ^ w.2.1 : ℚ)⁻¹)) :=
      (Computable.fst.pair ((Computable.snd.comp Computable.snd).pair
        (Computable.const (2 * ε)))).pair
        (computable_rat_inv_two_pow.comp (Computable.fst.comp Computable.snd))
    have h2 := (hA.lowerSemicomputable_bowenBall (μ := μ)).comp hmap.computableIn
    have heq : C = fun w : ℕ × ℕ × ℕ ↦ 1 ≤ w.1 ∧ (((2 ^ w.2.1 : ℚ)⁻¹ : ℚ) : ℝ) <
        (μ (bowenBall T w.1 (P.ι w.2.2) ((2 * ε : ℚ) : ℝ))).toReal := by
      funext w
      refine propext (and_congr_right' ?_)
      have hpow : (2 : ℝ≥0∞)⁻¹ ^ w.2.1 = ENNReal.ofReal (((2 ^ w.2.1 : ℚ)⁻¹ : ℚ) : ℝ) := by
        push_cast
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.inv_pow]
      rw [hpow, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (measure_ne_top μ _)]
    rw [heq]
    exact h1.and h2
  -- the decision procedure on Bowen distances of ideal points
  have hdist := birkhoff_computableIn_dist P T (fun _ : Fin 0 ↦ fun _ ↦ (0 : ℝ)) A
    ⟨hA.1, hA.2.1, fun j ↦ j.elim0⟩
  obtain ⟨dec, hdecC, hdecS⟩ := exists_dec_far_near hdist hε
  obtain ⟨e, he, henum⟩ := (relative_enumeration A C).mp hC
  obtain ⟨-, hok⟩ := computableIn_greedyList e dec he hdecC
  refine ⟨fun v ↦ ∃ t, v ∈ greedyList e dec t, ?_, ?_, ?_⟩
  · refine (relative_enumeration A _).mpr ⟨greedyEnum e dec, ?_,
      fun v ↦ exists_mem_greedyList_iff e dec v⟩
    have h := computable_in_cond hok he (ComputableIn.const none)
    exact h.of_eq fun t ↦ rfl
  · intro n k s hs
    have hSC : ∀ j ∈ s, C (n, k, j) := by
      intro j hj
      obtain ⟨t, ht⟩ := hs j hj
      obtain ⟨t', ht'⟩ := exists_eq_some_of_mem_greedyList e dec ht
      exact (henum _).mpr ⟨t', ht'⟩
    by_cases hn : 1 ≤ n
    swap
    · rcases s.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
      · simp
      · exact absurd (hSC j hj).1 hn
    choose! τ hτ using hs
    have hmem : ∀ j ∈ s, (n, k, j) ∈ greedyList e dec (s.sup τ) := fun j hj ↦
      greedyList_mono e dec (Finset.le_sup hj) (hτ j hj)
    have hpair := greedyList_pairwise e dec
      (fun n i j ↦ 4 * (ε : ℝ) < bowenDist T n (P.ι i) (P.ι j))
      (fun n i j h ↦ by rwa [bowen_dist_comm]) (fun n i j h ↦ (hdecS (n, i, j)).1 h) (s.sup τ)
    refine card_le_two_pow_of_far T hT μ hμ hn k P.ι s (fun j hj ↦ (hSC j hj).2) ?_
    intro j hj j' hj' hne
    have := hpair _ (hmem j hj) _ (hmem j' hj') rfl rfl hne
    push_cast
    linarith
  · intro x n k hn hk
    obtain ⟨i, hi⟩ := bowen_ball_dense P T hT x n hn ε hε'
    have hsub : bowenBall T n x ε ⊆ bowenBall T n (P.ι i) ((2 * ε : ℚ) : ℝ) := by
      intro y hy
      rw [bowen_ball_dense_iff T n hn] at hy hi ⊢
      have htri := bowen_ball_dense_triangle T n (P.ι i) x y
      rw [bowen_dist_comm T n (P.ι i) x] at htri
      push_cast
      linarith
    have hCi : C (n, k, i) := ⟨hn, hk.trans_le (measure_mono hsub)⟩
    obtain ⟨t, ht⟩ := (henum _).mp hCi
    obtain ⟨⟨n', k', j⟩, hv, h1, h2, hv'⟩ := exists_mem_greedyList_of_eq_some e dec ht
    simp only at h1 h2
    subst h1 h2
    have hnear : bowenDist T n' (P.ι i) (P.ι j) < 5 * (ε : ℝ) := by
      rcases hv' with hvw | hfalse
      · simp only [Prod.mk.injEq] at hvw
        rw [hvw.2.2, bowenDist_self_eq_zero]
        positivity
      · exact (hdecS _).2 hfalse
    refine ⟨j, ⟨t + 1, hv⟩, ?_⟩
    rw [bowen_ball_dense_iff T n' hn] at hi ⊢
    have htri := bowen_ball_dense_triangle T n' x (P.ι i) (P.ι j)
    linarith

/-! ### Coding the selected centres -/

/-- The cost of a member of the slice `(n, k)`: `k + 2 (⌊log₂ n⌋ + 1) + 2 (⌊log₂ (k+1)⌋ + 1)`. -/
def selCost (n k : ℕ) : ℕ := k + 2 * (Nat.log 2 n + 1) + 2 * (Nat.log 2 (k + 1) + 1)

/-- The code of a triple `(n, k, j)`: the pair code of `j` and of the Cantor pair of `n, k`. -/
def selCode (v : ℕ × ℕ × ℕ) : BitString := pairCode (natBits v.2.2) (natBits (Nat.pair v.1 v.2.1))

/-- The cost read off a bitstring through the second component of its pair code. -/
def selCostBits (b : BitString) : ℕ :=
  selCost (Nat.unpair (decodeBits (decodeSecond b))).1 (Nat.unpair (decodeBits (decodeSecond b))).2

/-- The cost of the code of a triple is the cost of its slice. -/
lemma selCostBits_selCode (v : ℕ × ℕ × ℕ) : selCostBits (selCode v) = selCost v.1 v.2.1 := by
  simp [selCostBits, selCode, decodeSecond_pairCode, natBits, decodeBits_natBits, Nat.unpair_pair]

/-- The cost read off bitstrings is primitive recursive. -/
lemma primrec_selCostBits : Primrec selCostBits := by
  have hcost : Primrec fun nk : ℕ × ℕ ↦ selCost nk.1 nk.2 := by
    have h := Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp
        (primrec_natLogTwo.comp Primrec.fst))))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp
        (primrec_natLogTwo.comp (Primrec.succ.comp Primrec.snd))))
    exact h.of_eq fun nk ↦ rfl
  have hb : Primrec fun b : BitString ↦ Nat.unpair (decodeBits (decodeSecond b)) :=
    Primrec.unpair.comp (primrec_decodeBits.comp CodedFiniteDistribution.decodeSecond_primrec)
  exact (hcost.comp hb).of_eq fun b ↦ rfl

/-- The weights `2^{-(k + 2 (⌊log₂ m⌋ + 1))}` summed over a slice of at most `2^k` members
leave the summable factor `2^{-2 (⌊log₂ m⌋ + 1)}`. -/
lemma tsum_inv_two_pow_log_lt_top :
    ∑' m : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (2 * (Nat.log 2 m + 1)) < ⊤ := by
  let r : ℕ → ℝ := fun m ↦ (2⁻¹ : ℝ) ^ (2 * (Nat.log 2 m + 1))
  have hr0 : ∀ m, 0 ≤ r m := fun m ↦ by positivity
  have hrle : ∀ m : ℕ, r m ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
    intro m
    have hm : (m : ℝ) + 1 ≤ 2 ^ (Nat.log 2 m + 1) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self one_lt_two m)
    calc r m = 1 / ((2 : ℝ) ^ (Nat.log 2 m + 1)) ^ 2 := by
          simp only [r, one_div, ← inv_pow, ← pow_mul, mul_comm]
      _ ≤ 1 / ((m : ℝ) + 1) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hm 2)
  have hsum : Summable fun m : ℕ ↦ 1 / ((m : ℝ) + 1) ^ 2 := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact h.congr fun m ↦ by push_cast; rfl
  have hr : Summable r := Summable.of_nonneg_of_le hr0 hrle hsum
  have heq : ∀ m, (2 : ℝ≥0∞)⁻¹ ^ (2 * (Nat.log 2 m + 1)) = ENNReal.ofReal (r m) := by
    intro m
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg hr0 hr]
  exact ENNReal.ofReal_lt_top

/-- Coding an enumerable set of triples with at most `2^k` members in each slice `(n, k)`:
the complexity of each member's index is bounded by the cost of its slice up to a constant. -/
lemma exists_complexity_le_selCost (A : Set ℕ) (S : ℕ × ℕ × ℕ → Prop) (hS : IsREIn A S)
    (hcard : ∀ (n k : ℕ) (s : Finset ℕ), (∀ j ∈ s, S (n, k, j)) → s.card ≤ 2 ^ k) :
    ∃ c : ℕ, ∀ n k j, S (n, k, j) → (oracleNatComplexity A j : ℝ) ≤ selCost n k + c := by
  classical
  let F : BitString → Prop := fun b ↦ ∃ v, S v ∧ selCode v = b
  have hcode : Computable selCode :=
    Computable₂.comp pairCode_computable
      (natBits_computable.comp (Computable.snd.comp Computable.snd))
      (natBits_computable.comp (Primrec₂.natPair.to_comp.comp Computable.fst
        (Computable.fst.comp Computable.snd)))
  have hF : IsREIn A F := hS.image hcode
  let g : Subtype F → ℝ := fun b ↦ (selCostBits b.val : ℝ)
  have hg : IsUpperSemicomputableOnIn A F g := by
    have hlt : Computable fun bq : BitString × ℚ ↦ decide (((selCostBits bq.1 : ℕ) : ℚ) < bq.2) :=
      computable₂_ratLt.comp (computable_nat_to_rat.comp
        (primrec_selCostBits.to_comp.comp Computable.fst)) Computable.snd
    refine ⟨fun bq ↦ F bq.1 ∧ ((selCostBits bq.1 : ℕ) : ℚ) < bq.2,
      (hF.comp ComputableIn.fst).and (isREIn_of_computable_decide hlt), ?_, ?_⟩
    · rintro b q ⟨hb, hq⟩
      refine ⟨hb, ?_⟩
      have hq' : ((selCostBits b : ℕ) : ℚ) < q := hq
      change ((selCostBits b : ℕ) : ℝ) < q
      exact_mod_cast hq'
    · intro b δ hδ
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_add_of_pos_right (g b) hδ)
      refine ⟨q, ⟨b.property, ?_⟩, hq2⟩
      have hq1' : ((selCostBits b.val : ℕ) : ℝ) < q := hq1
      change ((selCostBits b.val : ℕ) : ℚ) < q
      exact_mod_cast hq1'
  -- the mass
  let wt : ℕ × ℕ × ℕ → ℝ≥0∞ := fun v ↦ (2 : ℝ≥0∞)⁻¹ ^ selCost v.1 v.2.1
  let M : ℝ≥0∞ := ∑' v : ℕ × ℕ × ℕ, {v | S v}.indicator wt v
  have hM : ∑' b : Subtype F, (2 : ℝ≥0∞) ^ (-g b) ≤ M := by
    choose v hvS hvcode using fun b : Subtype F ↦ b.property
    let f : Subtype F → {v | S v} := fun b ↦ ⟨v b, hvS b⟩
    have hf : Function.Injective f := by
      intro b b' hbb'
      have h : v b = v b' := congrArg Subtype.val hbb'
      exact Subtype.ext ((hvcode b).symm.trans (h ▸ hvcode b'))
    have hterm : ∀ b : Subtype F, (2 : ℝ≥0∞) ^ (-g b) = wt (f b).val := by
      intro b
      simp only [g, wt, f]
      rw [← hvcode b, selCostBits_selCode, ENNReal.rpow_neg, ENNReal.rpow_natCast,
        ENNReal.inv_pow]
    calc ∑' b : Subtype F, (2 : ℝ≥0∞) ^ (-g b) = ∑' b : Subtype F, wt (f b).val :=
          tsum_congr hterm
      _ ≤ ∑' u : {v | S v}, wt u.val :=
          ENNReal.tsum_comp_le_tsum_of_injective hf fun u : {v | S v} ↦ wt u.val
      _ = M := tsum_subtype _ _
  let a : ℕ → ℝ≥0∞ := fun m ↦ (2 : ℝ≥0∞)⁻¹ ^ (2 * (Nat.log 2 m + 1))
  have hinner : ∀ n k, ∑' j : ℕ, {v | S v}.indicator wt (n, k, j) ≤ a n * a (k + 1) := by
    intro n k
    have hsplit : (2 : ℝ≥0∞)⁻¹ ^ selCost n k * 2 ^ k = a n * a (k + 1) := by
      have h1 : (2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k = 1 := by
        rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (by simp) (by simp)]
      calc (2 : ℝ≥0∞)⁻¹ ^ selCost n k * 2 ^ k =
            ((2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k) * (a n * a (k + 1)) := by
            simp only [selCost, a, pow_add]
            ring
        _ = a n * a (k + 1) := by rw [h1, one_mul]
    rw [← hsplit, ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s ↦ ?_
    have hs : ∑ j ∈ s, {v | S v}.indicator wt (n, k, j) =
        ∑ _j ∈ s.filter fun j ↦ S (n, k, j), (2 : ℝ≥0∞)⁻¹ ^ selCost n k := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [Set.indicator_apply, wt]
    rw [hs, Finset.sum_const, nsmul_eq_mul, mul_comm]
    gcongr
    exact_mod_cast hcard n k _ fun j hj ↦ (Finset.mem_filter.mp hj).2
  have hMfin : M < ⊤ := by
    have ha := tsum_inv_two_pow_log_lt_top
    calc M = ∑' n : ℕ, ∑' k : ℕ, ∑' j : ℕ, {v | S v}.indicator wt (n, k, j) := by
          rw [show M = ∑' v : ℕ × ℕ × ℕ, {v | S v}.indicator wt v from rfl, ENNReal.tsum_prod']
          exact tsum_congr fun n ↦ ENNReal.tsum_prod'
      _ ≤ ∑' n : ℕ, ∑' k : ℕ, a n * a (k + 1) :=
          ENNReal.tsum_le_tsum fun n ↦ ENNReal.tsum_le_tsum fun k ↦ hinner n k
      _ = (∑' n : ℕ, a n) * ∑' k : ℕ, a (k + 1) := by
          simp_rw [ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_mul_right]
      _ < ⊤ := ENNReal.mul_lt_top ha
          ((ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1) a).trans_lt ha)
  obtain ⟨c, hc⟩ := oracle_coding_finite_mass A F g hg M hM hMfin
  obtain ⟨d, hd⟩ := oracle_tuple_bounds A
  refine ⟨c + d, fun n k j hj ↦ ?_⟩
  have hw : F (selCode (n, k, j)) := ⟨_, hj, rfl⟩
  have hcode' := hc ⟨selCode (n, k, j), hw⟩
  change (oracleComplexity A (selCode (n, k, j)) : ℝ) ≤ (selCostBits (selCode (n, k, j)) : ℝ) + c
    at hcode'
  rw [selCostBits_selCode] at hcode'
  have hproj :
      (oracleNatComplexity A j : ℝ) ≤ (oracleComplexity A (selCode (n, k, j)) : ℝ) + d := by
    exact_mod_cast hd j (Nat.pair n k)
  push_cast
  linarith

/-- Coding by measure (Lemma 3.1), in the form used for limits: if `2^{-k}` is less than the
measure of the Bowen ball of radius `ε` about `x`, then the orbit complexity of `x` at radius
`6ε` is at most `k + 2 log₂ n + 2 log₂ (k + 1) + c`. Blueprint node `meas:coding`. -/
theorem coding_by_measure (P : Presentation X) (T : X → X) (hT : Continuous T) (A : Set ℕ)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1) (hA : IsMeasureAdmissible P T μ A)
    (ε : ℚ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (x : X) (n k : ℕ), 1 ≤ n →
      (2 : ℝ≥0∞)⁻¹ ^ k < μ (bowenBall T n x (ε : ℝ)) →
      (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) ≤
        k + 2 * Real.logb 2 n + 2 * Real.logb 2 (k + 1) + c := by
  obtain ⟨S, hS, hcard, hcover⟩ := exists_selection P T hT A μ hμ hA ε hε
  obtain ⟨c, hc⟩ := exists_complexity_le_selCost A S hS hcard
  refine ⟨c + 4, fun x n k hn hk ↦ ?_⟩
  obtain ⟨j, hj, hball⟩ := hcover x n k hn hk
  have h1 : (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) ≤ oracleNatComplexity A j := by
    exact_mod_cast orbitComplexityNat_le_of_mem P T A hball
  have h2 := hc n k j hj
  have h3 : (selCost n k : ℝ) ≤ k + 2 * Real.logb 2 n + 2 * Real.logb 2 (k + 1) + 4 := by
    have a1 := Real.natLog_le_logb n 2
    have a2 := Real.natLog_le_logb (k + 1) 2
    simp only [selCost]
    push_cast at a1 a2 ⊢
    linarith
  push_cast
  linarith

/-- Coding by measure (Lemma 3.1) as printed: with `I = -log₂ μ(B_n(x, T, ε))`,
`K_n^A(x, T, 6ε) ≤ I + 2 log₂ n + 2 log₂ (I + 2) + c`. Blueprint node `meas:coding`. -/
theorem coding_by_measure_info (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (x : X) (n : ℕ), 1 ≤ n → μ (bowenBall T n x (ε : ℝ)) ≠ 0 →
      (orbitComplexityNat P T A x n (6 * (ε : ℝ)) : ℝ) ≤
        -Real.logb 2 (μ (bowenBall T n x (ε : ℝ))).toReal + 2 * Real.logb 2 n +
          2 * Real.logb 2 (-Real.logb 2 (μ (bowenBall T n x (ε : ℝ))).toReal + 2) + c := by
  obtain ⟨c, hc⟩ := coding_by_measure P T hT A μ hμ hA ε hε
  refine ⟨c + 1, fun x n hn h0 ↦ ?_⟩
  set m := μ (bowenBall T n x (ε : ℝ)) with hm
  have hm_top : m ≠ ⊤ := measure_ne_top μ _
  have hr_pos : 0 < m.toReal := ENNReal.toReal_pos h0 hm_top
  have hr_le : m.toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top
      ((measure_mono (subset_univ (bowenBall T n x (ε : ℝ)))).trans hμ)
    rwa [ENNReal.toReal_one] at this
  set I := -Real.logb 2 m.toReal with hI
  have hI0 : 0 ≤ I := by
    have := Real.logb_nonpos one_lt_two hr_pos.le hr_le
    linarith
  set k := ⌊I⌋₊ + 1 with hk
  have hkI : I < k := by
    rw [hk]
    push_cast
    exact Nat.lt_floor_add_one I
  have hkI' : (k : ℝ) ≤ I + 1 := by
    rw [hk]
    push_cast
    linarith [Nat.floor_le hI0]
  have hpow : (2 : ℝ≥0∞)⁻¹ ^ k < m := by
    have hreal : (2 : ℝ)⁻¹ ^ k < m.toReal := by
      have h2 : (2 : ℝ)⁻¹ ^ k = (2 : ℝ) ^ (-(k : ℝ)) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
      rw [h2, ← Real.rpow_logb two_pos (by norm_num) hr_pos]
      exact (Real.rpow_lt_rpow_left_iff one_lt_two).mpr (by linarith)
    have hof : (2 : ℝ≥0∞)⁻¹ ^ k = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k) := by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
        ENNReal.ofReal_ofNat]
    rw [hof, ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hm_top]
    exact hreal
  have hbound := hc x n k hn hpow
  have hlog : Real.logb 2 ((k : ℝ) + 1) ≤ Real.logb 2 (I + 2) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  push_cast
  linarith

end Kolmogorov.PointToSet
