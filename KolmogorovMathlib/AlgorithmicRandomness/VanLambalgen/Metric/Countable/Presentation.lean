/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Countable.Defs
import KolmogorovMathlib.AlgorithmicRandomness.RatComputable
import KolmogorovMathlib.Interface.ComputableReals.Part01
import KolmogorovMathlib.Oracle.Closure
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Oracle

/-!
# The presentation of `ℕ → X`

The metric table of `Presentation.pi P` is computable relative to `A` when that of `P` is
(`Presentation.computablePresentationIn_pi`): the distance of two ideal sequences is a finite
sum up to a tail, since their coordinates agree beyond the longer list. A name of a sequence
computes a name of its truncation to the first `i` coordinates (`exists_isCauchyName_pi_below`).

## Conventions

The metric on `ℕ → X` is the local instance `PiCountable.metricSpace`, as in
`Metric/Countable/Defs.lean`. The approximation of the distance of two ideal sequences adds,
over the coordinates `j` below the longer list, the minimum of `2^{-j}` and the table value of
`P` at precision `p + j + 1`; the errors add up to less than `2^{-p}`.

## Main declarations

* `Presentation.computablePresentationIn_pi` (blueprint node `vlm:pi-presentation`).
* `exists_isCauchyName_pi_below` (blueprint node `vlm:pi-below`).

Used by `Metric/Countable/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability ENNReal

attribute [local instance] PiCountable.metricSpace

variable {X : Type*} [MetricSpace X] {P : Presentation X} {A : Set ℕ}

/-! ### Ideal sequences and their distances -/

/-- The list of indices decoded from the index of an ideal sequence. -/
private def piList (n : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) n).getD []

/-- Decoding the list of an ideal sequence is primitive recursive. -/
private lemma primrec_piList : Primrec piList :=
  (Primrec.option_getD.comp Primrec.decode (Primrec.const [])).of_eq fun _ => rfl

/-- The list of the index encoding a list is that list. -/
private lemma piList_encode (l : List ℕ) : piList (Encodable.encode l) = l := by
  simp [piList]

/-- The coordinates of an ideal sequence. -/
private lemma pi_ι_apply (n j : ℕ) : P.pi.ι n j = P.ι ((piList n).getD j 0) := rfl

/-- The distance on `ℕ → X`, with `encode j` written as `j`. -/
private lemma pi_dist_eq (x y : ℕ → X) :
    dist x y = ∑' j : ℕ, min ((2 : ℝ)⁻¹ ^ j) (dist (x j) (y j)) :=
  PiCountable.dist_eq_tsum x y

/-- The series of the distance on `ℕ → X` is summable. -/
private lemma pi_dist_summable (x y : ℕ → X) :
    Summable fun j : ℕ => min ((2 : ℝ)⁻¹ ^ j) (dist (x j) (y j)) :=
  PiCountable.dist_summable x y

/-- The distance of two ideal sequences is the finite sum over the coordinates below the longer
list: beyond it both coordinates are `P.ι 0`. -/
private lemma dist_pi_ι (n m : ℕ) :
    dist (P.pi.ι n) (P.pi.ι m) =
      ∑ j ∈ Finset.range (max (piList n).length (piList m).length),
        min ((2 : ℝ)⁻¹ ^ j) (dist (P.ι ((piList n).getD j 0)) (P.ι ((piList m).getD j 0))) := by
  rw [pi_dist_eq]
  refine tsum_eq_sum fun j hj => ?_
  have hj' : max (piList n).length (piList m).length ≤ j := by simpa using hj
  rw [pi_ι_apply, pi_ι_apply, List.getD_eq_default _ _ (le_of_max_le_left hj'),
    List.getD_eq_default _ _ (le_of_max_le_right hj'), dist_self]
  exact min_eq_right (by positivity)

/-! ### The rational approximation -/

/-- The partial sums approximating the distance of the ideal sequences of `l₁` and `l₂` at
precision `p`, from a table `q` of `P`. -/
private def piPartial (q : (ℕ × ℕ) × ℕ → ℚ) (l₁ l₂ : List ℕ) (p : ℕ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => piPartial q l₁ l₂ p j +
      min (2 ^ j : ℚ)⁻¹ (q ((l₁.getD j 0, l₂.getD j 0), p + j + 1))

/-- One step of the partial sums `piPartial`, with the lists decoded from the indices in `w`, as
a step function for `Nat.rec`. -/
private def piStep (q : (ℕ × ℕ) × ℕ → ℚ) (w : (ℕ × ℕ) × ℕ) (v : ℕ × ℚ) : ℚ :=
  v.2 + min (2 ^ v.1 : ℚ)⁻¹ (q (((piList w.1.1).getD v.1 0, (piList w.1.2).getD v.1 0),
    w.2 + v.1 + 1))

/-- The partial sums are within `2^{-p} - 2^{-(p+n)}` of the true partial sums. -/
private lemma piPartial_err {q : (ℕ × ℕ) × ℕ → ℚ}
    (hq : ∀ (ij : ℕ × ℕ) (p : ℕ),
      |(q (ij, p) : ℝ) - dist (P.ι ij.1) (P.ι ij.2)| < (2 : ℝ)⁻¹ ^ p)
    (l₁ l₂ : List ℕ) (p n : ℕ) :
    |(piPartial q l₁ l₂ p n : ℝ) - ∑ j ∈ Finset.range n,
        min ((2 : ℝ)⁻¹ ^ j) (dist (P.ι (l₁.getD j 0)) (P.ι (l₂.getD j 0)))| ≤
      (2 : ℝ)⁻¹ ^ p - (2 : ℝ)⁻¹ ^ (p + n) := by
  induction n with
  | zero => simp [piPartial]
  | succ n ih =>
    rw [piPartial, Finset.sum_range_succ]
    have h1 := hq (l₁.getD n 0, l₂.getD n 0) (p + n + 1)
    have h2 : |((min (2 ^ n : ℚ)⁻¹ (q ((l₁.getD n 0, l₂.getD n 0), p + n + 1)) : ℚ) : ℝ) -
        min ((2 : ℝ)⁻¹ ^ n) (dist (P.ι (l₁.getD n 0)) (P.ι (l₂.getD n 0)))| <
        (2 : ℝ)⁻¹ ^ (p + n + 1) := by
      push_cast
      rw [← inv_pow]
      refine (abs_min_sub_min_le_max _ _ _ _).trans_lt ?_
      simpa using h1
    have h3 : (2 : ℝ)⁻¹ ^ (p + n) = 2 * (2 : ℝ)⁻¹ ^ (p + n + 1) := by
      rw [pow_succ]; ring
    have h4 : (2 : ℝ)⁻¹ ^ (p + (n + 1)) = (2 : ℝ)⁻¹ ^ (p + n + 1) := by ring_nf
    rw [h4, Rat.cast_add, add_sub_add_comm]
    exact (abs_add_le _ _).trans (by linarith)

/-- The presentation of `ℕ → X` has a metric table computable relative to `A` when `P` has: the
distance of two ideal sequences is a finite sum, their coordinates agreeing beyond the longer
list. Blueprint node `vlm:pi-presentation`. -/
theorem Presentation.computablePresentationIn_pi (hP : ComputablePresentationIn P A) :
    ComputablePresentationIn P.pi A := by
  obtain ⟨qP, hqP, hP'⟩ := hP
  refine ⟨fun w => piPartial qP (piList w.1.1) (piList w.1.2) w.2
    (max (piList w.1.1).length (piList w.1.2).length), ?_, fun ij p => ?_⟩
  · have harg : Primrec fun u : ((ℕ × ℕ) × ℕ) × (ℕ × ℚ) =>
        (((piList u.1.1.1).getD u.2.1 0, (piList u.1.1.2).getD u.2.1 0), u.1.2 + u.2.1 + 1) :=
      (((Primrec.list_getD 0).comp (primrec_piList.comp
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) (Primrec.fst.comp Primrec.snd)).pair
        ((Primrec.list_getD 0).comp (primrec_piList.comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) (Primrec.fst.comp Primrec.snd))).pair
        (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)) (Primrec.const 1))
    have hq := hqP.comp harg.computableIn
    have hpow : Computable fun u : ((ℕ × ℕ) × ℕ) × (ℕ × ℚ) => (2 ^ u.2.1 : ℚ)⁻¹ :=
      computable_rat_inv_two_pow.comp (Computable.fst.comp Computable.snd)
    have hmin := ComputableIn₂.comp
      (ComputableReals.primrec_ratMin.to_comp.computableIn₂ (O := {charOracle A}))
      hpow.computableIn hq
    have hstep := ComputableIn₂.comp
      (computable₂_ratAdd.computableIn₂ (O := {charOracle A}))
      (ComputableIn.snd.comp ComputableIn.snd) hmin
    have hlen : Primrec fun w : (ℕ × ℕ) × ℕ =>
        max (piList w.1.1).length (piList w.1.2).length :=
      Primrec.nat_max.comp
        (Primrec.list_length.comp (primrec_piList.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.list_length.comp (primrec_piList.comp (Primrec.snd.comp Primrec.fst)))
    have hh : ComputableIn₂ {charOracle A} (piStep qP) :=
      ComputableIn₂.mk (f := piStep qP) (hstep.of_eq fun _ => rfl)
    have hrec := ComputableIn.nat_rec (h := piStep qP) hlen.computableIn
      (ComputableIn.const (O := {charOracle A}) (0 : ℚ)) hh
    refine hrec.of_eq fun w => ?_
    generalize max (piList w.1.1).length (piList w.1.2).length = n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [piPartial, ← ih]
      rfl
  · change |(piPartial qP (piList ij.1) (piList ij.2) p
      (max (piList ij.1).length (piList ij.2).length) : ℝ) - dist (P.pi.ι ij.1) (P.pi.ι ij.2)| <
      (2 : ℝ)⁻¹ ^ p
    rw [dist_pi_ι]
    exact (piPartial_err hP' _ _ p _).trans_lt (sub_lt_self _ (by positivity))

/-! ### Truncating a name -/

/-- The coordinates of a truncated list. -/
private lemma getD_take (l : List ℕ) (i j : ℕ) :
    (l.take i).getD j 0 = if j < i then l.getD j 0 else 0 := by
  by_cases hj : j < i <;> simp [List.getD_eq_getElem?_getD, hj]

/-- A Cauchy name of a sequence `y` computes, relative to `A`, a Cauchy name of its truncation
`j ↦ if j < i then y j else P.ι 0`: keep the first `i` entries of each listed ideal sequence.
Blueprint node `vlm:pi-below`. -/
theorem exists_isCauchyName_pi_below {y : ℕ → X} {a : ℕ → ℕ} (ha : IsCauchyName P.pi y a)
    (i : ℕ) :
    ∃ b, IsCauchyName P.pi (fun j => if j < i then y j else P.ι 0) b ∧
      charOracle (oracleJoin A (nameOracle b)) ≤ᵀ charOracle (oracleJoin A (nameOracle a)) := by
  refine ⟨fun p => Encodable.encode ((piList (a p)).take i), fun p => ?_, ?_⟩
  · refine lt_of_le_of_lt ?_ (ha p)
    rw [pi_dist_eq, pi_dist_eq]
    refine Summable.tsum_le_tsum (fun j => ?_) (pi_dist_summable _ _) (pi_dist_summable _ _)
    simp only [pi_ι_apply, piList_encode, getD_take]
    by_cases hj : j < i
    · simp [hj]
    · simp only [hj, ↓reduceIte, dist_self]
      rw [min_eq_right (by positivity)]
      exact le_min (by positivity) dist_nonneg
  · have hacomp := computableIn_nameOracle_oracleJoin A a
    have hg : Primrec fun n : ℕ => Encodable.encode ((piList n).take i) :=
      Primrec.encode.comp (Primrec.list_take.comp (Primrec.const i) primrec_piList)
    exact oracle_joins_least A _ _ (oracle_joins A _)
      (charOracle_nameOracle_le ((hg.computableIn.comp hacomp).of_eq fun _ => rfl))

end Kolmogorov.PointToSet
