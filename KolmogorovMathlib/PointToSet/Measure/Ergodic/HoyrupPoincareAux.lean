/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupBasic
import KolmogorovMathlib.PointToSet.Measure.Ergodic.SymbolicLowerBoundEffective
import KolmogorovMathlib.Ergodic.MeanErgodic

/-!
# Effective Poincaré recurrence: the one-step estimate

Auxiliary material for `HoyrupPoincare` (BDHMS, Theorem 7, on the binary shift), in the namespace
`Kolmogorov.PointToSet.PoincareAux`. For a word `u`, a length `n` and a threshold `k`:

* `cnt u n v`: the number of positions `j ≤ n` at which `u` occurs in the word `v`; on
  `x↾(n + |u|)` it is the Birkhoff sum `∑_{j ≤ n} 1_{[u]}(σ^j x)` (`cnt_cast_eq_birkhoffSum`).
* `badSet u n k = {x | cnt u n (x↾(n + |u|)) > k}`; its measure is the finite sum `badMass ν`
  of the cylinder measures over `badWords u n k` (`badMass_eq`, through `boolWords N`, the list
  of all words of length `N`), hence an `A`-computable real family
  (`isComputableRealFamilyIn_badMass`).
* `mul_measure_trap_le`: for a `σ`-invariant `ν` and `trapSet U n = ⋂_{i≤n} σ^{-i} U`,
  `(n+1) ν([u] ∩ trapSet U n) ≤ ∑_{j≤n} ν(σ^{-j}[u] ∩ σ^{-n} U) = ∫_{σ^{-n} U} cnt
  ≤ k ν(U) + (n+1) ν(badSet u n k)`.
* `good ν s r (u, n)`: there are `k` and rationals `β > ν(badSet u n k)`, `e < ν[u]` with
  `k s + (n+1) β < (n+1) r e`. It is `A`-r.e. (`isREIn_good`); when `ν(U) ≤ s` it gives
  `ν([u] ∩ trapSet U n) ≤ r ν[u]` (`measure_trap_le_of_good`); and for an ergodic `ν` it holds
  for some `n` as soon as `ν[u] > 0` (`exists_good`: the `L¹` mean ergodic theorem
  `tendsto_integral_abs_birkhoffAverage_sub` and Markov's inequality, with
  `k = ⌈(n+1)(ν[u] + γ)⌉`, `γ = (r - s) ν[u] / 8`).

This replaces the `L¹` criterion `∫ |a_n - ν[u]| < (r - s) ν[u]` of BDHMS by a count threshold,
so that only sums of cylinder measures have to be computed. Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

namespace PoincareAux

/-! ### Words and cylinders -/

/-- The prefix of length `k ≤ m` of `x↾m` is `x↾k`. -/
lemma wordPrefix_take (x : ℕ → Bool) {k m : ℕ} (h : k ≤ m) :
    (wordPrefix x m).take k = wordPrefix x k := by
  apply List.ext_getElem (by simp [wordPrefix, h])
  intro i h1 h2
  simp [wordPrefix]

/-- Dropping `l` letters of `x↾m` gives `(σ^l x)↾(m - l)`. -/
lemma wordPrefix_drop (x : ℕ → Bool) (l m : ℕ) :
    (wordPrefix x m).drop l = wordPrefix (shiftMap^[l] x) (m - l) := by
  apply List.ext_getElem (by simp [wordPrefix])
  intro i h1 h2
  simp [wordPrefix, SymbolicLower.iterate_shift, add_comm]

/-- `x ∈ [u]` iff `u` is the prefix of `x` of length `|u|`. -/
lemma mem_listCylinder_iff {u : List Bool} {x : ℕ → Bool} :
    x ∈ listCylinder u ↔ wordPrefix x u.length = u := by
  constructor
  · intro h
    apply List.ext_getElem (by simp [wordPrefix])
    intro i h1 h2
    simp [wordPrefix, h i h2]
  · intro h i hi
    have := List.getElem_of_eq h (i := i) (by simpa [wordPrefix] using hi)
    simpa [wordPrefix] using this

/-- `u` is a prefix of `x↾m` iff `|u| ≤ m` and `x ∈ [u]`. -/
lemma prefix_wordPrefix_iff {u : List Bool} {x : ℕ → Bool} {m : ℕ} :
    u <+: wordPrefix x m ↔ u.length ≤ m ∧ x ∈ listCylinder u := by
  rw [mem_listCylinder_iff]
  constructor
  · intro h
    have hl : u.length ≤ m := by simpa [wordPrefix] using h.length_le
    refine ⟨hl, ?_⟩
    rw [← wordPrefix_take x hl]
    exact (List.prefix_iff_eq_take.mp h).symm
  · rintro ⟨hl, h⟩
    rw [← h, ← wordPrefix_take x hl]
    exact List.take_prefix _ _

/-- `w` is a prefix of `(x↾m)` from position `l` on iff `|w| ≤ m - l` and `σ^l x ∈ [w]`. -/
lemma prefix_drop_wordPrefix_iff {w : List Bool} {x : ℕ → Bool} {l m : ℕ} :
    w <+: (wordPrefix x m).drop l ↔ w.length ≤ m - l ∧ shiftMap^[l] x ∈ listCylinder w := by
  rw [wordPrefix_drop, prefix_wordPrefix_iff]

/-- The cylinder of a word extended by one letter. -/
lemma listCylinder_append_singleton (v : List Bool) (b : Bool) :
    listCylinder (v ++ [b]) = listCylinder v ∩ {x | x v.length = b} := by
  ext x
  simp only [mem_listCylinder_iff, mem_inter_iff, mem_ofPred_eq, List.length_append,
    List.length_singleton]
  simp only [wordPrefix, List.ofFn_succ', List.concat_eq_append]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    refine ⟨h1, ?_⟩
    simpa using h2
  · rintro ⟨h1, h2⟩
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    rw [h1, h2]

/-- Cylinders are measurable. -/
lemma measurableSet_listCylinder (v : List Bool) : MeasurableSet (listCylinder v) :=
  PointToSet.measurableSet_listCylinder v

/-- A union of cylinders over any set of words is measurable. -/
lemma measurableSet_biUnion_listCylinder (S : Set (List Bool)) :
    MeasurableSet (⋃ w ∈ S, listCylinder w) :=
  MeasurableSet.biUnion (Set.to_countable S) fun w _ ↦ measurableSet_listCylinder w

/-- Two cylinders that meet have comparable words. -/
lemma prefix_or_prefix_of_mem {u v : List Bool} {x : ℕ → Bool} (hu : x ∈ listCylinder u)
    (hv : x ∈ listCylinder v) : u <+: v ∨ v <+: u := by
  have hu' : u <+: wordPrefix x (u.length + v.length) :=
    prefix_wordPrefix_iff.mpr ⟨by omega, hu⟩
  have hv' : v <+: wordPrefix x (u.length + v.length) :=
    prefix_wordPrefix_iff.mpr ⟨by omega, hv⟩
  exact List.prefix_or_prefix_of_prefix hu' hv'

/-- Cylinders are antitone along prefixes. -/
lemma listCylinder_subset_of_prefix {u v : List Bool} (h : u <+: v) :
    listCylinder v ⊆ listCylinder u := by
  intro x hx
  rw [mem_listCylinder_iff] at hx
  rw [← hx] at h
  exact (prefix_wordPrefix_iff.mp h).2

/-! ### All words of a given length -/

/-- One step of `boolWords`: extend every word by one letter at the end. -/
def extendWords (W : List (List Bool)) : List (List Bool) :=
  W.flatMap fun v ↦ [v ++ [false], v ++ [true]]

/-- All binary words of length `N`. -/
def boolWords (N : ℕ) : List (List Bool) :=
  extendWords^[N] [[]]

/-- `boolWords` is primitive recursive. -/
lemma primrec_boolWords : Primrec boolWords := by
  have hinner : Primrec₂ fun (_ : List (List Bool)) (v : List Bool) ↦
      [v ++ [false], v ++ [true]] :=
    (Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [false]))
      (Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [true]))
        (Primrec.const []))).to₂
  have hstep : Primrec extendWords := Primrec.list_flatMap Primrec.id hinner
  exact (Primrec.nat_iterate' hstep).comp (Primrec.const [[]]) Primrec.id

/-- `boolWords (N + 1)` in terms of `boolWords N`. -/
lemma boolWords_succ (N : ℕ) : boolWords (N + 1) = extendWords (boolWords N) := by
  simp only [boolWords]
  rw [Function.iterate_succ_apply']

/-- The words of `boolWords N` have length `N`. -/
lemma length_of_mem_boolWords {N : ℕ} {v : List Bool} (h : v ∈ boolWords N) :
    v.length = N := by
  induction N generalizing v with
  | zero =>
    simp only [boolWords, Function.iterate_zero, id_eq, List.mem_cons, List.not_mem_nil,
      or_false] at h
    simp [h]
  | succ N ih =>
    rw [boolWords_succ, extendWords, List.mem_flatMap] at h
    obtain ⟨u, hu, hv⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> simp [ih hu]

/-- `((l.flatMap g).map F).sum = ∑_{a ∈ l} ((g a).map F).sum`. -/
lemma sum_map_flatMap' {δ ε M : Type*} [AddCommMonoid M] (l : List δ) (g : δ → List ε)
    (F : ε → M) : ((l.flatMap g).map F).sum = (l.map fun a ↦ ((g a).map F).sum).sum :=
  SymbolicLower.sum_map_flatMap l g F

/-- The measure of a set is the sum of the measures of its intersections with the cylinders of
length `N`. -/
lemma measure_eq_sum_boolWords (ν : Measure (ℕ → Bool)) (S : Set (ℕ → Bool)) (N : ℕ) :
    ν S = ((boolWords N).map fun v ↦ ν (S ∩ listCylinder v)).sum := by
  induction N with
  | zero =>
    have : listCylinder ([] : List Bool) = univ := by ext x; simp [listCylinder]
    simp [boolWords, this]
  | succ N ih =>
    rw [ih, boolWords_succ, extendWords, sum_map_flatMap']
    congr 1
    refine List.map_congr_left fun v _ ↦ ?_
    have hC : MeasurableSet {x : ℕ → Bool | x v.length = false} :=
      measurableSet_eq_fun (measurable_pi_apply v.length) measurable_const
    rw [← measure_inter_add_sdiff (S ∩ listCylinder v) hC]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 2
    · ext x; simp [listCylinder_append_singleton, and_assoc]
    · ext x; simp [listCylinder_append_singleton, and_assoc]

/-- Summing a function that vanishes off a filter. -/
lemma sum_map_eq_sum_filter {δ M : Type*} [AddCommMonoid M] (l : List δ) (q : δ → Bool)
    (f g : δ → M) (h : ∀ v ∈ l, f v = if q v then g v else 0) :
    (l.map f).sum = ((l.filter q).map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ih fun v hv ↦ h v (by simp [hv]), h a (by simp),
      List.filter_cons]
    cases q a <;> simp

/-- A set defined through the prefix of length `N` is the union of the corresponding cylinders. -/
lemma setOf_wordPrefix_eq (p : List Bool → Prop) (N : ℕ) :
    {x : ℕ → Bool | p (wordPrefix x N)} = ⋃ v ∈ {v : List Bool | p v ∧ v.length = N},
      listCylinder v := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  constructor
  · intro h
    exact ⟨wordPrefix x N, ⟨h, by simp [wordPrefix]⟩, mem_listCylinder_wordPrefix x N⟩
  · rintro ⟨v, ⟨hv, hl⟩, hx⟩
    rw [mem_listCylinder_iff, hl] at hx
    rwa [hx]

/-- A set defined through the prefix of length `N` is measurable. -/
lemma measurableSet_setOf_wordPrefix (p : List Bool → Prop) (N : ℕ) :
    MeasurableSet {x : ℕ → Bool | p (wordPrefix x N)} := by
  rw [setOf_wordPrefix_eq]
  exact measurableSet_biUnion_listCylinder _

/-- The measure of a set defined through the prefix of length `N` is a finite sum of cylinder
measures. -/
lemma measure_setOf_wordPrefix (ν : Measure (ℕ → Bool)) (p : List Bool → Prop) [DecidablePred p]
    (N : ℕ) :
    ν {x | p (wordPrefix x N)} =
      (((boolWords N).filter fun v ↦ decide (p v)).map fun v ↦ ν (listCylinder v)).sum := by
  rw [measure_eq_sum_boolWords ν _ N]
  refine sum_map_eq_sum_filter _ _ _ _ fun v hv ↦ ?_
  have hl := length_of_mem_boolWords hv
  by_cases hp : p v
  · simp only [hp, decide_true, ite_true]
    congr 1
    refine inter_eq_right.mpr fun x hx ↦ ?_
    rw [mem_listCylinder_iff, hl] at hx
    simpa [hx] using hp
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    convert measure_empty (μ := ν)
    refine eq_empty_of_forall_notMem fun x ⟨hx1, hx2⟩ ↦ hp ?_
    rw [mem_listCylinder_iff, hl] at hx2
    simpa [hx2] using hx1

/-- `toReal` of a finite list sum of finite terms. -/
lemma toReal_list_sum {δ : Type*} (l : List δ) (f : δ → ℝ≥0∞) (hf : ∀ v, f v ≠ ∞) :
    (l.map f).sum.toReal = (l.map fun v ↦ (f v).toReal).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, ENNReal.toReal_add (hf a), ih, List.map_cons,
      List.sum_cons]
    clear ih
    induction t with
    | nil => simp
    | cons b t ih => simpa [ENNReal.add_eq_top, hf b] using ih

/-! ### Counting occurrences of a word -/

/-- Whether the word `u` occurs in `v` at position `j`. -/
def occurs (u v : List Bool) (j : ℕ) : Bool :=
  decide ((v.drop j).take u.length = u)

/-- The number of positions `j ≤ n` at which `u` occurs in `v`. -/
def cnt (u : List Bool) (n : ℕ) (v : List Bool) : ℕ :=
  ((List.range (n + 1)).filter (occurs u v)).length

/-- In `x↾(n + |u|)`, the word `u` occurs at position `j ≤ n` iff `σ^j x ∈ [u]`. -/
lemma occurs_wordPrefix_iff {u : List Bool} {x : ℕ → Bool} {n j : ℕ} (hj : j ≤ n) :
    occurs u (wordPrefix x (n + u.length)) j = true ↔ shiftMap^[j] x ∈ listCylinder u := by
  rw [occurs, decide_eq_true_iff, eq_comm, ← List.prefix_iff_eq_take,
    prefix_drop_wordPrefix_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by omega, h⟩⟩

/-- The length of a filter of `List.range N` as a finite sum. -/
lemma length_filter_range (q : ℕ → Bool) (N : ℕ) :
    ((List.range N).filter q).length = ∑ j ∈ Finset.range N, if q j then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ,
      List.filter_cons]
    cases q N <;> simp

/-- The count of occurrences as a sum of indicators in `ℝ≥0∞`. -/
lemma cnt_cast_eq_sum_indicator (u : List Bool) (n : ℕ) (x : ℕ → Bool) :
    (cnt u n (wordPrefix x (n + u.length)) : ℝ≥0∞) =
      ∑ j ∈ Finset.range (n + 1), (shiftMap^[j] ⁻¹' listCylinder u).indicator 1 x := by
  rw [cnt, length_filter_range, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases h : shiftMap^[j] x ∈ listCylinder u
  · have h1 := (occurs_wordPrefix_iff hj').mpr h
    simp [h1, indicator_of_mem (show x ∈ shiftMap^[j] ⁻¹' listCylinder u from h)]
  · have h1 : ¬ occurs u (wordPrefix x (n + u.length)) j = true :=
      fun h' ↦ h ((occurs_wordPrefix_iff hj').mp h')
    simp [h1, indicator_of_notMem (show x ∉ shiftMap^[j] ⁻¹' listCylinder u from h)]

/-- The count of occurrences is the Birkhoff sum of the indicator of `[u]`. -/
lemma cnt_cast_eq_birkhoffSum (u : List Bool) (n : ℕ) (x : ℕ → Bool) :
    (cnt u n (wordPrefix x (n + u.length)) : ℝ) =
      birkhoffSum shiftMap ((listCylinder u).indicator 1) (n + 1) x := by
  rw [cnt, length_filter_range, Nat.cast_sum, birkhoffSum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases h : shiftMap^[j] x ∈ listCylinder u
  · have h1 := (occurs_wordPrefix_iff hj').mpr h
    simp [h1, indicator_of_mem h]
  · have h1 : ¬ occurs u (wordPrefix x (n + u.length)) j = true :=
      fun h' ↦ h ((occurs_wordPrefix_iff hj').mp h')
    simp [h1, indicator_of_notMem h]

/-- The count is at most the number `n + 1` of positions. -/
lemma cnt_le (u : List Bool) (n : ℕ) (v : List Bool) : cnt u n v ≤ n + 1 := by
  rw [cnt]
  exact (List.length_filter_le _ _).trans (by simp)

/-! ### Words with too many occurrences -/

/-- The words of length `n + |u|` in which `u` occurs at more than `k` positions `j ≤ n`. -/
def badWords (u : List Bool) (n k : ℕ) : List (List Bool) :=
  (boolWords (n + u.length)).filter fun v ↦ decide (k < cnt u n v)

/-- The sequences in which `u` occurs at more than `k` positions `j ≤ n`. -/
def badSet (u : List Bool) (n k : ℕ) : Set (ℕ → Bool) :=
  {x | k < cnt u n (wordPrefix x (n + u.length))}

/-- The measure of `badSet`, as a finite sum of cylinder measures. -/
noncomputable def badMass (ν : Measure (ℕ → Bool)) (z : (List Bool × ℕ) × ℕ) : ℝ :=
  ((badWords z.1.1 z.1.2 z.2).map fun v ↦ (ν (listCylinder v)).toReal).sum

/-- `badMass` is the measure of `badSet`. -/
lemma badMass_eq (ν : Measure (ℕ → Bool)) [IsFiniteMeasure ν] (u : List Bool) (n k : ℕ) :
    badMass ν ((u, n), k) = ν.real (badSet u n k) := by
  rw [measureReal_def, badSet, measure_setOf_wordPrefix ν (fun v ↦ k < cnt u n v),
    toReal_list_sum _ _ fun v ↦ measure_ne_top ν _]
  rfl

/-- `badSet` is measurable. -/
lemma measurableSet_badSet (u : List Bool) (n k : ℕ) : MeasurableSet (badSet u n k) :=
  measurableSet_setOf_wordPrefix (fun v ↦ k < cnt u n v) _

/-! ### The recurrence bound -/

/-- The sequences whose first `n + 1` iterates `x, σx, …, σⁿx` lie in `U`. -/
def trapSet (U : Set (ℕ → Bool)) (n : ℕ) : Set (ℕ → Bool) :=
  {x | ∀ i ≤ n, shiftMap^[i] x ∈ U}

/-- `trapSet U n` is antitone in `n`. -/
lemma trapSet_anti (U : Set (ℕ → Bool)) {m n : ℕ} (h : m ≤ n) : trapSet U n ⊆ trapSet U m :=
  fun _ hx i hi ↦ hx i (hi.trans h)

/-- The basic estimate: `(n+1) ν([u] ∩ ⋂_{i≤n} σ^{-i} U) ≤ k ν(U) + (n+1) ν(badSet u n k)`. -/
lemma mul_measure_trap_le {ν : Measure (ℕ → Bool)} (hσ : MeasurePreserving shiftMap ν ν)
    {U : Set (ℕ → Bool)} (hU : MeasurableSet U) (u : List Bool) (n k : ℕ) :
    ((n : ℝ≥0∞) + 1) * ν (listCylinder u ∩ trapSet U n) ≤
      k * ν U + ((n : ℝ≥0∞) + 1) * ν (badSet u n k) := by
  set Y := shiftMap^[n] ⁻¹' U with hY
  have hYm : MeasurableSet Y := (SymbolicLower.measurable_shift.iterate n) hU
  have hcyl := measurableSet_listCylinder u
  have hA : ∀ j, MeasurableSet (shiftMap^[j] ⁻¹' listCylinder u) :=
    fun j ↦ (SymbolicLower.measurable_shift.iterate j) hcyl
  -- each term of the average dominates the measure of the trap
  have h1 : ∀ i ∈ Finset.range (n + 1), ν (listCylinder u ∩ trapSet U n) ≤
      ν (shiftMap^[n - i] ⁻¹' listCylinder u ∩ Y) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpre : shiftMap^[n - i] ⁻¹' (listCylinder u ∩ shiftMap^[i] ⁻¹' U) =
        shiftMap^[n - i] ⁻¹' listCylinder u ∩ Y := by
      rw [preimage_inter, ← preimage_comp, ← Function.iterate_add, Nat.add_sub_cancel' hi']
    calc ν (listCylinder u ∩ trapSet U n) ≤ ν (listCylinder u ∩ shiftMap^[i] ⁻¹' U) :=
          measure_mono (inter_subset_inter_right _ fun x hx ↦ hx i hi')
      _ = ν (shiftMap^[n - i] ⁻¹' (listCylinder u ∩ shiftMap^[i] ⁻¹' U)) :=
          ((hσ.iterate (n - i)).measure_preimage
            (hcyl.inter ((SymbolicLower.measurable_shift.iterate i) hU)).nullMeasurableSet).symm
      _ = _ := by rw [hpre]
  have h2 : ((n : ℝ≥0∞) + 1) * ν (listCylinder u ∩ trapSet U n) ≤
      ∑ j ∈ Finset.range (n + 1), ν (shiftMap^[j] ⁻¹' listCylinder u ∩ Y) := by
    have := Finset.card_nsmul_le_sum _ _ _ h1
    rw [Finset.card_range, nsmul_eq_mul] at this
    rw [← Finset.sum_range_reflect] at this
    refine (le_of_eq ?_).trans (this.trans (le_of_eq (Finset.sum_congr rfl fun j hj ↦ ?_)))
    · push_cast; ring
    · have hj' := Finset.mem_range.mp hj
      rw [show n - (n + 1 - 1 - j) = j by omega]
  -- the sum is the integral of the count over `Y`
  have h3 : ∑ j ∈ Finset.range (n + 1), ν (shiftMap^[j] ⁻¹' listCylinder u ∩ Y) =
      ∫⁻ x in Y, (cnt u n (wordPrefix x (n + u.length)) : ℝ≥0∞) ∂ν := by
    simp_rw [cnt_cast_eq_sum_indicator]
    rw [lintegral_finsetSum _ fun j _ ↦ measurable_one.indicator (hA j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [lintegral_indicator_one (hA j), Measure.restrict_apply (hA j)]
  -- pointwise, the count is at most `k`, or at most `n + 1` on `badSet`
  have h4 : ∀ x, (cnt u n (wordPrefix x (n + u.length)) : ℝ≥0∞) ≤
      k + ((n : ℝ≥0∞) + 1) * (badSet u n k).indicator 1 x := by
    intro x
    by_cases hx : x ∈ badSet u n k
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      have := cnt_le u n (wordPrefix x (n + u.length))
      calc (cnt u n (wordPrefix x (n + u.length)) : ℝ≥0∞) ≤ ((n + 1 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast this
        _ ≤ _ := by push_cast; exact le_add_self
    · rw [indicator_of_notMem hx, mul_zero, add_zero]
      exact_mod_cast not_lt.mp hx
  have h5 : ∫⁻ x in Y, (cnt u n (wordPrefix x (n + u.length)) : ℝ≥0∞) ∂ν ≤
      k * ν U + ((n : ℝ≥0∞) + 1) * ν (badSet u n k) := by
    calc ∫⁻ x in Y, (cnt u n (wordPrefix x (n + u.length)) : ℝ≥0∞) ∂ν
        ≤ ∫⁻ x in Y, (k + ((n : ℝ≥0∞) + 1) * (badSet u n k).indicator 1 x) ∂ν :=
          lintegral_mono h4
      _ = k * ν Y + ((n : ℝ≥0∞) + 1) * (ν.restrict Y) (badSet u n k) := by
          rw [lintegral_add_left measurable_const, lintegral_const_mul _
            (measurable_one.indicator (measurableSet_badSet u n k)),
            lintegral_indicator_one (measurableSet_badSet u n k), lintegral_const,
            Measure.restrict_apply MeasurableSet.univ, univ_inter]
      _ ≤ k * ν U + ((n : ℝ≥0∞) + 1) * ν (badSet u n k) := by
          rw [hY, (hσ.iterate n).measure_preimage hU.nullMeasurableSet]
          gcongr
          exact Measure.restrict_le_self
  exact h2.trans (h3.le.trans h5)

/-! ### The search predicate -/

/-- The search predicate for a word `u` and a length `n`: a count threshold `k` and rationals
`β > ν(badSet u n k)` and `e < ν[u]` with `k s + (n + 1) β < (n + 1) r e`. -/
def good (ν : Measure (ℕ → Bool)) (s r : ℚ) (z : List Bool × ℕ) : Prop :=
  ∃ y : ℕ × ℚ × ℚ, badMass ν ((z.1, z.2), y.1) < y.2.1 ∧
    (y.2.2 : ℝ) < (ν (listCylinder z.1)).toReal ∧
    (y.1 : ℚ) * s + ((z.2 : ℚ) + 1) * y.2.1 < ((z.2 : ℚ) + 1) * r * y.2.2

/-- Soundness of the search: if `good ν s r (u, n)` and `ν(U) ≤ s`, then
`ν([u] ∩ ⋂_{i≤n} σ^{-i} U) ≤ r ν[u]`. -/
lemma measure_trap_le_of_good {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν]
    (hσ : MeasurePreserving shiftMap ν ν) {U : Set (ℕ → Bool)} (hU : MeasurableSet U)
    {s r : ℚ} (hr : 0 < r) (hUs : ν.real U ≤ s) {u : List Bool} {n : ℕ}
    (hg : good ν s r (u, n)) :
    ν (listCylinder u ∩ trapSet U n) ≤ ENNReal.ofReal r * ν (listCylinder u) := by
  obtain ⟨⟨k, β, e⟩, h1, h2, h3⟩ := hg
  have hkey := mul_measure_trap_le hσ hU u n k
  have hreal : ((n : ℝ) + 1) * ν.real (listCylinder u ∩ trapSet U n) ≤
      k * ν.real U + ((n : ℝ) + 1) * ν.real (badSet u n k) := by
    have := ENNReal.toReal_mono (by finiteness) hkey
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at this
    have hN : ((n : ℝ≥0∞) + 1).toReal = n + 1 := by
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simp
    simpa [ENNReal.toReal_mul, measureReal_def, hN] using this
  rw [badMass_eq] at h1
  have h3' : (k : ℝ) * s + ((n : ℝ) + 1) * β < ((n : ℝ) + 1) * r * e := by exact_mod_cast h3
  set p := (ν (listCylinder u)).toReal with hp
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hW : ν.real (listCylinder u ∩ trapSet U n) ≤ r * p := by
    have : ((n : ℝ) + 1) * ν.real (listCylinder u ∩ trapSet U n) ≤ ((n : ℝ) + 1) * (r * p) := by
      calc ((n : ℝ) + 1) * ν.real (listCylinder u ∩ trapSet U n)
          ≤ k * ν.real U + ((n : ℝ) + 1) * ν.real (badSet u n k) := hreal
        _ ≤ k * s + ((n : ℝ) + 1) * β := by
            gcongr
        _ ≤ ((n : ℝ) + 1) * r * e := h3'.le
        _ ≤ ((n : ℝ) + 1) * (r * p) := by
            rw [mul_assoc]
            gcongr
    exact le_of_mul_le_mul_left this hn
  calc ν (listCylinder u ∩ trapSet U n) = ENNReal.ofReal (ν.real (listCylinder u ∩ trapSet U n)) :=
        (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (r * p) := ENNReal.ofReal_le_ofReal hW
    _ = ENNReal.ofReal r * ν (listCylinder u) := by
        rw [ENNReal.ofReal_mul hr'.le, hp, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The search halts on every cylinder of positive measure (mean ergodic theorem in `L¹` and
Markov's inequality). -/
lemma exists_good {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν)
    {s r : ℚ} (hs0 : 0 ≤ s) (hsr : s < r) (hr1 : r ≤ 1) {u : List Bool}
    (hpos : 0 < ν (listCylinder u)) : ∃ n, good ν s r (u, n) := by
  set p := (ν (listCylinder u)).toReal with hp_def
  have hp : 0 < p := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hp1 : p ≤ 1 := by
    rw [hp_def, ← measureReal_def]
    exact measureReal_le_one
  have hs0' : (0 : ℝ) ≤ s := by exact_mod_cast hs0
  have hsr' : (s : ℝ) < r := by exact_mod_cast hsr
  have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  set γ : ℝ := ((r : ℝ) - s) * p / 8 with hγ
  have hγ0 : 0 < γ := div_pos (mul_pos (sub_pos.mpr hsr') hp) (by norm_num)
  set g : (ℕ → Bool) → ℝ := (listCylinder u).indicator 1 with hg_def
  have hgm : Measurable g := measurable_one.indicator (measurableSet_listCylinder u)
  have hgC : ∀ x, |g x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ listCylinder u <;> simp [g, hx]
  have hint : ∫ y, g y ∂ν = p := by
    rw [hg_def, integral_indicator_one (measurableSet_listCylinder u), measureReal_def]
  have hT := Kolmogorov.Ergodic.tendsto_integral_abs_birkhoffAverage_sub hν hgm hgC
  rw [hint] at hT
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.mp (hT.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < γ ^ 2)))
  set n := N₀ + ⌈γ⁻¹⌉₊ with hn_def
  have hn : (0 : ℝ) < n + 1 := by positivity
  set B := birkhoffAverage ℝ shiftMap g (n + 1) with hB_def
  have hB : ∀ x, B x = (cnt u n (wordPrefix x (n + u.length)) : ℝ) / (n + 1) := by
    intro x
    rw [hB_def, birkhoffAverage, cnt_cast_eq_birkhoffSum, smul_eq_mul, div_eq_inv_mul]
    push_cast
    ring
  have hB01 : ∀ x, 0 ≤ B x ∧ B x ≤ 1 := by
    intro x
    rw [hB x]
    refine ⟨by positivity, (div_le_one hn).mpr ?_⟩
    exact_mod_cast cnt_le u n _
  have hBm : Measurable B := by
    have hs : Measurable (birkhoffSum shiftMap g (n + 1)) :=
      Finset.measurable_sum _ fun k _ ↦ hgm.comp (SymbolicLower.measurable_shift.iterate k)
    have hBe : B = fun x ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * birkhoffSum shiftMap g (n + 1) x := by
      funext x
      rw [hB_def, birkhoffAverage, smul_eq_mul]
    rw [hBe]
    exact measurable_const.mul hs
  have hInt : Integrable (fun x ↦ |B x - p|) ν := by
    refine Integrable.of_bound
      (continuous_abs.measurable.comp (hBm.sub measurable_const)).aestronglyMeasurable 2
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have := hB01 x
    constructor <;> linarith
  have hsmall : ∫ x, |B x - p| ∂ν ≤ γ ^ 2 := hN₀ (n + 1) (by omega)
  set k := ⌈((n : ℝ) + 1) * (p + γ)⌉₊ with hk_def
  -- the bad set is small
  have hbad : badMass ν ((u, n), k) ≤ γ := by
    rw [badMass_eq]
    have hM := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x ↦ abs_nonneg _) hInt γ
    have hsub : badSet u n k ⊆ {x | γ ≤ |B x - p|} := by
      intro x hx
      have hx2 : k < cnt u n (wordPrefix x (n + u.length)) := hx
      have hx3 : (k : ℝ) < cnt u n (wordPrefix x (n + u.length)) := by exact_mod_cast hx2
      have hx' : ((n : ℝ) + 1) * (p + γ) < cnt u n (wordPrefix x (n + u.length)) :=
        (Nat.le_ceil _).trans_lt hx3
      have : p + γ < B x := by
        rw [hB x, lt_div_iff₀ hn]
        linarith
      change γ ≤ |B x - p|
      exact le_trans (by linarith) (le_abs_self _)
    have hle := measureReal_mono (μ := ν) hsub
    have : γ * ν.real {x | γ ≤ |B x - p|} ≤ γ * γ := by nlinarith
    nlinarith [le_of_mul_le_mul_left this hγ0]
  obtain ⟨β, hβ1, hβ2⟩ := exists_rat_btwn (show badMass ν ((u, n), k) < badMass ν ((u, n), k) + γ
    by linarith)
  obtain ⟨e, he1, he2⟩ := exists_rat_btwn (show p - γ < p by linarith)
  refine ⟨n, ⟨k, β, e⟩, hβ1, he2, ?_⟩
  -- the arithmetic
  have hk : (k : ℝ) ≤ ((n : ℝ) + 1) * (p + γ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hNγ : 1 ≤ ((n : ℝ) + 1) * γ := by
    have h1 : γ⁻¹ ≤ (n : ℝ) + 1 := by
      have : (⌈γ⁻¹⌉₊ : ℝ) ≤ n := by exact_mod_cast Nat.le_add_left _ _
      linarith [Nat.le_ceil γ⁻¹]
    calc (1 : ℝ) = γ⁻¹ * γ := (inv_mul_cancel₀ hγ0.ne').symm
      _ ≤ ((n : ℝ) + 1) * γ := mul_le_mul_of_nonneg_right h1 hγ0.le
  have hk2 : (k : ℝ) ≤ ((n : ℝ) + 1) * (p + 2 * γ) := by linarith
  have h1 : (k : ℝ) * s ≤ ((n : ℝ) + 1) * (p + 2 * γ) * s := mul_le_mul_of_nonneg_right hk2 hs0'
  have h2 : ((n : ℝ) + 1) * β < ((n : ℝ) + 1) * (2 * γ) :=
    mul_lt_mul_of_pos_left (by linarith) hn
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hs0' hsr'
  have h3 : ((n : ℝ) + 1) * r * (p - γ) < ((n : ℝ) + 1) * r * e :=
    mul_lt_mul_of_pos_left he1 (mul_pos hn hr0)
  have h4 : (p + 2 * γ) * s + 2 * γ ≤ r * (p - γ) := by
    have h5 : γ * (2 * s + 2 + r) ≤ γ * 5 :=
      mul_le_mul_of_nonneg_left (by linarith) hγ0.le
    have h6 : γ * 8 = r * p - s * p := by rw [hγ]; ring
    nlinarith
  have h4' : ((n : ℝ) + 1) * ((p + 2 * γ) * s + 2 * γ) ≤ ((n : ℝ) + 1) * (r * (p - γ)) :=
    mul_le_mul_of_nonneg_left h4 hn.le
  have hfin : (k : ℝ) * s + ((n : ℝ) + 1) * β < ((n : ℝ) + 1) * r * e := by nlinarith
  exact_mod_cast hfin

/-! ### Effectivity of the search predicate -/

/-- `occurs` is primitive recursive. -/
lemma primrec_occurs : Primrec fun q : (List Bool × List Bool) × ℕ ↦ occurs q.1.1 q.1.2 q.2 :=
  (Primrec.eq.comp (Primrec.list_take.comp (Primrec.list_length.comp (Primrec.fst.comp
    Primrec.fst)) (Primrec.list_drop.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
    (Primrec.fst.comp Primrec.fst)).decide

/-- `cnt` is primitive recursive. -/
lemma primrec_cnt : Primrec fun q : (List Bool × ℕ) × List Bool ↦ cnt q.1.1 q.1.2 q.2 := by
  have hl : Primrec fun q : (List Bool × ℕ) × List Bool ↦ List.range (q.1.2 + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
  have hp : Primrec₂ fun (q : (List Bool × ℕ) × List Bool) (j : ℕ) ↦ occurs q.1.1 q.2 j :=
    (primrec_occurs.comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to₂
  exact Primrec.list_length.comp (Primrec.list_filter hl hp)

/-- `badWords` is primitive recursive. -/
lemma primrec_badWords :
    Primrec fun z : (List Bool × ℕ) × ℕ ↦ badWords z.1.1 z.1.2 z.2 := by
  have hl : Primrec fun z : (List Bool × ℕ) × ℕ ↦ boolWords (z.1.2 + z.1.1.length) :=
    primrec_boolWords.comp (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
  have hp : Primrec₂ fun (z : (List Bool × ℕ) × ℕ) (v : List Bool) ↦
      decide (z.2 < cnt z.1.1 z.1.2 v) :=
    (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst)
      (primrec_cnt.comp (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd))).decide.to₂
  exact Primrec.list_filter hl hp

/-- `badMass ν` is an `A`-computable real family when `ν` is `A`-computable on cylinders. -/
lemma isComputableRealFamilyIn_badMass {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    (hc : IsComputableWordMeasureIn A ν) : IsComputableRealFamilyIn A (badMass ν) := by
  have h := SymbolicLower.isComputableRealFamilyIn_listSum hc primrec_badWords.to_comp 1
    (by norm_num)
  simp only [Rat.cast_one, one_mul] at h
  exact h

/-- The search predicate is `A`-r.e. -/
lemma isREIn_good {A : Set ℕ} {ν : Measure (ℕ → Bool)} (hc : IsComputableWordMeasureIn A ν)
    (s r : ℚ) : IsREIn A (good ν s r) := by
  have h1 : IsREIn A fun w : (List Bool × ℕ) × (ℕ × ℚ × ℚ) ↦
      badMass ν ((w.1.1, w.1.2), w.2.1) < w.2.2.1 :=
    (birkhoff_computableIn_lt A _ (isComputableRealFamilyIn_badMass hc)).comp
      (f := fun w : (List Bool × ℕ) × (ℕ × ℚ × ℚ) ↦ (((w.1.1, w.1.2), w.2.1), w.2.2.1))
      (((((Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd)).pair
          (Computable.fst.comp (Computable.snd.comp Computable.snd))).computableIn)
  have h2 : IsREIn A fun w : (List Bool × ℕ) × (ℕ × ℚ × ℚ) ↦
      (w.2.2.2 : ℝ) < (ν (listCylinder w.1.1)).toReal :=
    (birkhoff_computableIn_gt A _ hc).comp
      (f := fun w : (List Bool × ℕ) × (ℕ × ℚ × ℚ) ↦ (w.1.1, w.2.2.2))
      (((Computable.fst.comp Computable.fst).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd))).computableIn)
  have hN : Computable fun w : (List Bool × ℕ) × (ℕ × ℚ × ℚ) ↦ ((w.1.2 : ℚ) + 1) :=
    computable₂_ratAdd.comp (computable_nat_to_rat.comp (Computable.snd.comp Computable.fst))
      (Computable.const 1)
  have h3 : IsREIn A fun w : (List Bool × ℕ) × (ℕ × ℚ × ℚ) ↦
      (w.2.1 : ℚ) * s + ((w.1.2 : ℚ) + 1) * w.2.2.1 < ((w.1.2 : ℚ) + 1) * r * w.2.2.2 :=
    isREIn_of_computable_decide (computable₂_ratLt.comp
      (computable₂_ratAdd.comp (computable₂_ratMul.comp
        (computable_nat_to_rat.comp (Computable.fst.comp Computable.snd)) (Computable.const s))
        (computable₂_ratMul.comp hN (Computable.fst.comp (Computable.snd.comp Computable.snd))))
      (computable₂_ratMul.comp (computable₂_ratMul.comp hN (Computable.const r))
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  exact (h1.and (h2.and h3)).exists

end PoincareAux

end Kolmogorov.PointToSet
