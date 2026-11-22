/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness

/-!
# Hoyrup's theorem: lower semicomputable functions, null cylinders, Levin–Schnorr

First part of the formalization of M. Hoyrup, *The dimension of ergodic random sequences*
(STACS 2012, arXiv:1107.1149), relativized to an oracle `A`, on binary sequences `ℕ → Bool` with
the cylinder tests of `WordRandomness`.

* `IsLscFunFamilyIn A v`, `IsLscFunIn A v`: `v : (ℕ → Bool) → ℝ≥0∞` is lower semicomputable relative
  to `A` (uniformly in an index): every set `{x | q < v x}`, `q` rational, is a union of cylinders
  `[w]` over an `A`-r.e. set of words, uniformly in `q`. Closure under reindexing
  (`IsLscFunFamilyIn.comp`, `.apply`), r.e. suprema (`IsLscFunFamilyIn.iSup`, `.iSup_ge`),
  composition with iterates of the shift (`IsLscFunIn.comp_shiftMap_iterate`), finite sums
  (`IsLscFunFamilyIn.sum_range`), Birkhoff averages (`IsLscFunIn.shiftAverage`) and truncated
  subtraction `c - min(f, c)` of a function whose sets `{f < r}` are c.e. unions of cylinders
  (`isLscFunFamilyIn_natCast_sub_min`); rational constants (`isLscFunFamilyIn_const`).
  Lower semicomputable functions are measurable. Sums are handled with lists of rational lower
  bounds of the summands, each certified by a cylinder (or nonpositive).
* `listCylinder_wordPrefix_pos_of_mem_wordRandomPoints`: a random sequence meets no null cylinder;
  it follows from the Levin–Schnorr test below, which gives `ν[ω↾n] ≥ 2^{-K^A(ω↾n)-m} > 0`.
* `exists_infoBits_le_wordComplexity_add` (lower half of the Levin–Schnorr theorem, relativized):
  at a random sequence, `-log₂ ν[ω↾n] ≤ K^A(ω↾n) + c` (test `⋃ {[w] | ν[w] < 2^{-K^A(w)-m}}`,
  measure `≤ 2^{-m}` by `oracle_kraft`).

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- A family `v i` of functions on `ℕ → Bool` with values in `[0, ∞]` is uniformly lower
semicomputable relative to `A`: `{x | q < v i x} = ⋃_{w ∈ E(i, q)} [w]` for an `A`-r.e. relation
`E`. Blueprint node `erg:hoyrup`. -/
def IsLscFunFamilyIn {ι : Type*} [Primcodable ι] (A : Set ℕ)
    (v : ι → (ℕ → Bool) → ℝ≥0∞) : Prop :=
  ∃ E : (ι × ℚ) × List Bool → Prop, IsREIn A E ∧
    ∀ i (q : ℚ), {x | ENNReal.ofReal q < v i x} = ⋃ w ∈ {w | E ((i, q), w)}, listCylinder w

/-- A single lower semicomputable function relative to `A`. Blueprint node `erg:hoyrup`. -/
def IsLscFunIn (A : Set ℕ) (v : (ℕ → Bool) → ℝ≥0∞) : Prop :=
  IsLscFunFamilyIn A fun _ : Unit ↦ v

/-- The Birkhoff average `(1/n) ∑_{k<n} v(σ^k x)` in `[0, ∞]` (`0` for `n = 0`).
Blueprint node `erg:hoyrup`. -/
noncomputable def shiftAverage (v : (ℕ → Bool) → ℝ≥0∞) (n : ℕ) (x : ℕ → Bool) : ℝ≥0∞ :=
  (∑ k ∈ Finset.range n, v (shiftMap^[k] x)) / n

/-! ### Words and cylinders -/

/-- Iterates of the shift: `(σ^k x) j = x (j + k)`. -/
private theorem shiftMap_iterate_apply (x : ℕ → Bool) (k j : ℕ) : shiftMap^[k] x j = x (j + k) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [shiftMap, Nat.add_assoc]

/-- Membership in a cylinder means that the prefix of the same length is the word. -/
private theorem mem_listCylinder_iff_wordPrefix {x : ℕ → Bool} {w : List Bool} :
    x ∈ listCylinder w ↔ wordPrefix x w.length = w := by
  constructor
  · intro h
    refine List.ext_getElem (by simp [wordPrefix]) fun i h1 h2 ↦ ?_
    simp [wordPrefix, h i h2]
  · intro h i hi
    have := List.getElem_of_eq h (i := i) (by simpa [wordPrefix] using hi)
    simpa [wordPrefix] using this

/-- Prefixes of prefixes: `(x↾n).take m = x↾m` for `m ≤ n`. -/
private theorem take_wordPrefix (x : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n) :
    (wordPrefix x n).take m = wordPrefix x m := by
  apply List.ext_getElem
  · simp [wordPrefix, hmn]
  · intro k h1 h2
    simp [wordPrefix]

/-- Suffixes of prefixes: `(x↾(k+m)).drop k = (σ^k x)↾m`. -/
private theorem drop_wordPrefix (x : ℕ → Bool) (k m : ℕ) :
    (wordPrefix x (k + m)).drop k = wordPrefix (shiftMap^[k] x) m := by
  apply List.ext_getElem
  · simp [wordPrefix]
  · intro i h1 h2
    simp [wordPrefix, shiftMap_iterate_apply, Nat.add_comm]

/-- If `u` is a prefix of `w`, then `[w] ⊆ [u]`. -/
private theorem mem_listCylinder_of_take_eq {x : ℕ → Bool} {w u : List Bool}
    (hx : x ∈ listCylinder w) (h : w.take u.length = u) : x ∈ listCylinder u := by
  rw [mem_listCylinder_iff_wordPrefix] at hx ⊢
  have hle : u.length ≤ w.length := by
    have := congrArg List.length h
    simp only [List.length_take] at this
    omega
  conv_rhs => rw [← h, ← hx]
  rw [take_wordPrefix x hle]

/-- If `x ∈ [w]`, then `σ^k x ∈ [w.drop k]`. -/
private theorem shiftMap_iterate_mem_listCylinder_drop {x : ℕ → Bool} {w : List Bool}
    (hx : x ∈ listCylinder w) (k : ℕ) : shiftMap^[k] x ∈ listCylinder (w.drop k) := by
  intro i hi
  rw [shiftMap_iterate_apply, List.getElem_drop, Nat.add_comm]
  exact hx _ _

/-- Membership in a union of cylinders over a set of words. -/
private lemma hb_mem_biUnion {x : ℕ → Bool} {P : List Bool → Prop} :
    x ∈ ⋃ w ∈ {w | P w}, listCylinder w ↔ ∃ w, P w ∧ x ∈ listCylinder w := by
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop]

/-! ### Lower semicomputable functions -/

/-- Reindexing a lower semicomputable family along a computable map. Blueprint node
`erg:hoyrup`. -/
theorem IsLscFunFamilyIn.comp {ι κ : Type*} [Primcodable ι] [Primcodable κ] {A : Set ℕ}
    {v : ι → (ℕ → Bool) → ℝ≥0∞} (hv : IsLscFunFamilyIn A v) {f : κ → ι} (hf : Computable f) :
    IsLscFunFamilyIn A fun k ↦ v (f k) := by
  obtain ⟨E, hE, hEq⟩ := hv
  refine ⟨fun p ↦ E ((f p.1.1, p.1.2), p.2), hE.comp ?_, fun k q ↦ hEq (f k) q⟩
  exact (((hf.comp (Computable.fst.comp Computable.fst)).pair
    (Computable.snd.comp Computable.fst)).pair Computable.snd).computableIn

/-- A member of a lower semicomputable family is lower semicomputable. Blueprint node
`erg:hoyrup`. -/
theorem IsLscFunFamilyIn.apply {ι : Type*} [Primcodable ι] {A : Set ℕ}
    {v : ι → (ℕ → Bool) → ℝ≥0∞} (hv : IsLscFunFamilyIn A v) (i : ι) : IsLscFunIn A (v i) :=
  hv.comp (f := fun _ : Unit ↦ i) (Computable.const i)

/-- Constant families with values `ofReal r`, `r` rational, are lower semicomputable.
Blueprint node `erg:hoyrup`. -/
theorem isLscFunFamilyIn_const (A : Set ℕ) (r : ℚ) :
    IsLscFunFamilyIn A fun (_ : Unit) (_ : ℕ → Bool) ↦ ENNReal.ofReal r := by
  classical
  refine ⟨fun p ↦ p.1.2 < r ∧ 0 < r ∧ p.2 = [], ?_, fun _ q ↦ ?_⟩
  · refine isREIn_of_computable_decide ?_
    have h1 : Computable fun p : (Unit × ℚ) × List Bool ↦ decide (p.1.2 < r) :=
      computable₂_ratLt.comp (Computable.snd.comp Computable.fst) (Computable.const r)
    have h2 : Computable fun p : (Unit × ℚ) × List Bool ↦ decide (p.2 = []) :=
      (Primrec.eq.comp Primrec.snd (Primrec.const [])).decide.to_comp
    have h3 : Computable fun p : (Unit × ℚ) × List Bool ↦
        (decide (p.1.2 < r) && (decide ((0 : ℚ) < r) && decide (p.2 = []))) :=
      (Primrec.and.to_comp.comp h1 ((Primrec.and.to_comp.comp (Computable.const _) h2)))
    simpa only [Bool.decide_and] using h3
  · ext x
    rw [hb_mem_biUnion, mem_ofPred_eq, ENNReal.ofReal_lt_ofReal_iff']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨[], ⟨by exact_mod_cast h1, by exact_mod_cast h2, rfl⟩, fun i hi ↦ by simp at hi⟩
    · rintro ⟨w, ⟨h1, h2, -⟩, -⟩
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- An r.e. supremum of a uniformly lower semicomputable family is lower semicomputable,
uniformly in the remaining index. Blueprint node `erg:hoyrup`. -/
theorem IsLscFunFamilyIn.iSup {ι : Type*} [Primcodable ι] {A : Set ℕ}
    {v : ι × ℕ → (ℕ → Bool) → ℝ≥0∞} (hv : IsLscFunFamilyIn A v) :
    IsLscFunFamilyIn A fun i x ↦ ⨆ j, v (i, j) x := by
  obtain ⟨E, hE, hEq⟩ := hv
  refine ⟨fun p ↦ ∃ j, E (((p.1.1, j), p.1.2), p.2), ?_, fun i q ↦ ?_⟩
  · have h : IsREIn A fun z : ((ι × ℚ) × List Bool) × ℕ ↦ E (((z.1.1.1, z.2), z.1.1.2), z.1.2) :=
      hE.comp ((((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        Computable.snd).pair (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.comp Computable.fst)).computableIn
    exact h.exists
  · ext x
    rw [mem_ofPred_eq, lt_iSup_iff, hb_mem_biUnion]
    constructor
    · rintro ⟨j, hj⟩
      have : x ∈ {x | ENNReal.ofReal q < v (i, j) x} := hj
      rw [hEq, hb_mem_biUnion] at this
      obtain ⟨w, hw, hx⟩ := this
      exact ⟨w, ⟨j, hw⟩, hx⟩
    · rintro ⟨w, ⟨j, hw⟩, hx⟩
      refine ⟨j, ?_⟩
      have : x ∈ {x | ENNReal.ofReal q < v (i, j) x} := by
        rw [hEq, hb_mem_biUnion]
        exact ⟨w, hw, hx⟩
      exact this

/-- The supremum `⨆_{j ≥ N} v j` of a lower semicomputable family is lower semicomputable.
Blueprint node `erg:hoyrup`. -/
theorem IsLscFunFamilyIn.iSup_ge {A : Set ℕ} {v : ℕ → (ℕ → Bool) → ℝ≥0∞}
    (hv : IsLscFunFamilyIn A v) (N : ℕ) : IsLscFunIn A fun x ↦ ⨆ j ≥ N, v j x := by
  have h := (hv.comp (f := fun p : Unit × ℕ ↦ N + p.2)
    (Primrec.nat_add.comp (Primrec.const N) Primrec.snd).to_comp).iSup
  have heq : (fun (_ : Unit) (x : ℕ → Bool) ↦ ⨆ j ≥ N, v j x) =
      fun (i : Unit) x ↦ ⨆ j, v (N + (i, j).2) x := by
    funext i x
    apply le_antisymm
    · refine iSup₂_le fun j hj ↦ ?_
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      exact le_iSup (fun k ↦ v (N + k) x) k
    · exact iSup_le fun k ↦ le_iSup₂ (f := fun j (_ : j ≥ N) ↦ v j x) (N + k) (Nat.le_add_right _ _)
  unfold IsLscFunIn
  rw [heq]
  exact h

/-- Lower semicomputable families compose with the iterates of the shift, uniformly in the
number of iterations. Blueprint node `erg:hoyrup`. -/
theorem IsLscFunIn.comp_shiftMap_iterate {A : Set ℕ} {v : (ℕ → Bool) → ℝ≥0∞}
    (hv : IsLscFunIn A v) : IsLscFunFamilyIn A fun k x ↦ v (shiftMap^[k] x) := by
  obtain ⟨E, hE, hEq⟩ := hv
  classical
  refine ⟨fun p ↦ ∃ u, E (((), p.1.2), u) ∧ (p.2.drop p.1.1).take u.length = u, ?_,
    fun k q ↦ ?_⟩
  · have h1 : IsREIn A fun z : ((ℕ × ℚ) × List Bool) × List Bool ↦ E (((), z.1.1.2), z.2) :=
      hE.comp (((Computable.const ()).pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        Computable.snd).computableIn
    have h2 : IsREIn A fun z : ((ℕ × ℚ) × List Bool) × List Bool ↦
        (z.1.2.drop z.1.1.1).take z.2.length = z.2 := by
      exact isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_take.comp
        (Primrec.list_length.comp Primrec.snd)
        (Primrec.list_drop.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst))) Primrec.snd).decide.to_comp
    exact (h1.and h2).exists
  · have hv' : ∀ y, ENNReal.ofReal q < v y ↔ ∃ u, E (((), q), u) ∧ y ∈ listCylinder u :=
      fun y ↦ (Set.ext_iff.1 (hEq () q) y).trans hb_mem_biUnion
    ext x
    rw [mem_ofPred_eq, hv', hb_mem_biUnion]
    constructor
    · rintro ⟨u, hu, hxu⟩
      refine ⟨wordPrefix x (k + u.length), ⟨u, hu, ?_⟩, mem_listCylinder_wordPrefix _ _⟩
      rw [drop_wordPrefix, take_wordPrefix _ le_rfl, ← mem_listCylinder_iff_wordPrefix]
      exact hxu
    · rintro ⟨w, ⟨u, hu, htake⟩, hxw⟩
      exact ⟨u, hu, mem_listCylinder_of_take_eq (shiftMap_iterate_mem_listCylinder_drop hxw k)
        htake⟩

/-- Rational approximation from below of a finite sum in `[0, ∞]`: nonnegative rationals, each
`0` or strictly below its term, whose sum still exceeds `t`. -/
private lemma hb_exists_rat_lt_sum : ∀ (n : ℕ) (a : Fin n → ℝ≥0∞) (t : ℝ≥0∞), t < ∑ i, a i →
    ∃ r : Fin n → ℚ, (∀ i, 0 ≤ r i ∧ (r i = 0 ∨ ENNReal.ofReal (r i) < a i)) ∧
      t < ∑ i, ENNReal.ofReal (r i)
  | 0, a, t, h => by simp at h
  | n + 1, a, t, h => by
    rw [Fin.sum_univ_succ] at h
    by_cases ha : a 0 = 0
    · rw [ha, zero_add] at h
      obtain ⟨r, hr, hlt⟩ := hb_exists_rat_lt_sum n (fun i ↦ a i.succ) t h
      refine ⟨Fin.cons 0 r, fun i ↦ ?_, ?_⟩
      · refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp
        · simpa using hr j
      · simpa [Fin.sum_univ_succ] using hlt
    by_cases hs : ∑ i : Fin n, a i.succ = 0
    · rw [hs, add_zero] at h
      obtain ⟨q, hq0, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
      have h1' : t < ENNReal.ofReal q := h1
      have h2' : ENNReal.ofReal q < a 0 := h2
      refine ⟨Fin.cons q 0, fun i ↦ ?_, ?_⟩
      · refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact ⟨hq0, Or.inr (by simpa using h2')⟩
        · simp
      · simpa [Fin.sum_univ_succ] using h1'
    obtain ⟨y, hy, z, hz, hyz⟩ := ENNReal.exists_lt_add_of_lt_add h ha hs
    obtain ⟨q, hq0, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hy
    have h1' : y < ENNReal.ofReal q := h1
    have h2' : ENNReal.ofReal q < a 0 := h2
    obtain ⟨r, hr, hlt⟩ := hb_exists_rat_lt_sum n (fun i ↦ a i.succ) z hz
    refine ⟨Fin.cons q r, fun i ↦ ?_, ?_⟩
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact ⟨hq0, Or.inr (by simpa using h2')⟩
      · simpa using hr j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact hyz.trans (ENNReal.add_lt_add h1' hlt)

/-- The sum of a list of rationals bounded termwise: `ofReal (∑ qs) ≤ ∑_{k < |qs|} g k` when
`ofReal qs[k] ≤ g k`. -/
private lemma hb_ofReal_listSum_le : ∀ (qs : List ℚ) (g : ℕ → ℝ≥0∞),
    (∀ k (h : k < qs.length), ENNReal.ofReal (qs.get ⟨k, h⟩) ≤ g k) →
      ENNReal.ofReal (qs.sum : ℝ) ≤ ∑ k ∈ Finset.range qs.length, g k
  | [], g, _ => by simp
  | a :: l, g, h => by
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', Rat.cast_add, add_comm _ (g 0)]
    calc ENNReal.ofReal ((a : ℝ) + (l.sum : ℝ))
        ≤ ENNReal.ofReal a + ENNReal.ofReal (l.sum : ℝ) := ENNReal.ofReal_add_le
      _ ≤ g 0 + ∑ k ∈ Finset.range l.length, g (k + 1) := by
        refine add_le_add (by simpa using h 0 (by simp)) ?_
        exact hb_ofReal_listSum_le l (fun k ↦ g (k + 1)) fun k hk ↦ by
          simpa using h (k + 1) (by simpa using hk)

/-- The sum of a list of rationals is computable. -/
private lemma hb_computable_listSum : Computable fun l : List ℚ ↦ l.sum := by
  have h : Computable fun l : List ℚ ↦ List.foldl (fun s b ↦ (fun (_ : List ℚ) (p : ℚ × ℚ) ↦
      p.1 + p.2) l (s, b)) (0 : ℚ) l :=
    Computable.list_foldl Computable.id (Computable.const 0)
      (computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂
  refine h.of_eq fun l ↦ ?_
  rw [List.sum_eq_foldl]

/-- The witness relation for finite sums: a list `qs` of `n` rationals with sum above `q`, each
nonpositive or certified below its term by a prefix of `w`. -/
private def hbSumRel (E : (ℕ × ℚ) × List Bool → Prop)
    (p : ((ℕ × ℚ) × List Bool) × List ℚ) : Prop :=
  p.2.length = p.1.1.1 ∧ p.1.1.2 < p.2.sum ∧ 0 < p.2.sum ∧
    ∀ k (h : k < p.2.length), (fun z : ((ℕ × ℚ) × List Bool) × ℕ × ℚ ↦
      z.2.2 ≤ 0 ∨ ∃ u, E ((z.2.1, z.2.2), u) ∧ z.1.2.take u.length = u) (p.1, k, p.2.get ⟨k, h⟩)

/-- Finite sums `∑_{k<n} f k` of a lower semicomputable family are lower semicomputable,
uniformly in `n`. Blueprint node `erg:hoyrup`. -/
theorem IsLscFunFamilyIn.sum_range {A : Set ℕ} {f : ℕ → (ℕ → Bool) → ℝ≥0∞}
    (hf : IsLscFunFamilyIn A f) :
    IsLscFunFamilyIn A fun n x ↦ ∑ k ∈ Finset.range n, f k x := by
  obtain ⟨E, hE, hEq⟩ := hf
  classical
  refine ⟨fun p ↦ ∃ qs, hbSumRel E (p, qs), ?_, fun n q ↦ ?_⟩
  · have hF : IsREIn A fun z : ((ℕ × ℚ) × List Bool) × ℕ × ℚ ↦
        z.2.2 ≤ 0 ∨ ∃ u, E ((z.2.1, z.2.2), u) ∧ z.1.2.take u.length = u := by
      refine IsREIn.or (isREIn_of_computable_decide ?_) ?_
      · exact (ComputableReals.primrec_ratLe.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.const 0)).decide.to_comp
      · have h1 : IsREIn A fun y : (((ℕ × ℚ) × List Bool) × ℕ × ℚ) × List Bool ↦
            E ((y.1.2.1, y.1.2.2), y.2) :=
          hE.comp (((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
            (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
            Computable.snd).computableIn
        have h2 : IsREIn A fun y : (((ℕ × ℚ) × List Bool) × ℕ × ℚ) × List Bool ↦
            y.1.1.2.take y.2.length = y.2 :=
          isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_take.comp
            (Primrec.list_length.comp Primrec.snd)
            (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).decide.to_comp
        exact (h1.and h2).exists
    have h4 := IsREIn.list_forall_get hF
    have h1 : IsREIn A fun p : ((ℕ × ℚ) × List Bool) × List ℚ ↦ p.2.length = p.1.1.1 :=
      isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).decide.to_comp
    have h2 : IsREIn A fun p : ((ℕ × ℚ) × List Bool) × List ℚ ↦ p.1.1.2 < p.2.sum :=
      isREIn_of_computable_decide (computable₂_ratLt.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst))
        (hb_computable_listSum.comp Computable.snd))
    have h3 : IsREIn A fun p : ((ℕ × ℚ) × List Bool) × List ℚ ↦ 0 < p.2.sum :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (hb_computable_listSum.comp Computable.snd))
    exact (h1.and (h2.and (h3.and h4))).exists
  · have hfE : ∀ k (r : ℚ) y, ENNReal.ofReal r < f k y ↔
        ∃ u, E ((k, r), u) ∧ y ∈ listCylinder u := by
      intro k r y
      exact (Set.ext_iff.1 (hEq k r) y).trans hb_mem_biUnion
    ext x
    rw [mem_ofPred_eq, hb_mem_biUnion]
    beta_reduce
    constructor
    · intro h
      rw [← Fin.sum_univ_eq_sum_range] at h
      obtain ⟨r, hr, hlt⟩ := hb_exists_rat_lt_sum n (fun i ↦ f i x) _ h
      have hu : ∀ i : Fin n, ∃ u : List Bool,
          r i = 0 ∨ (E ((i, r i), u) ∧ x ∈ listCylinder u) := by
        intro i
        rcases (hr i).2 with h0 | hlt'
        · exact ⟨[], Or.inl h0⟩
        · obtain ⟨u, hu, hxu⟩ := (hfE i (r i) x).1 hlt'
          exact ⟨u, Or.inr ⟨hu, hxu⟩⟩
      choose U hU using hu
      set M := Finset.univ.sup fun i ↦ (U i).length
      have hsum : ENNReal.ofReal ((List.ofFn r).sum : ℝ) = ∑ i, ENNReal.ofReal (r i) := by
        rw [List.sum_ofFn, Rat.cast_sum,
          ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by exact_mod_cast (hr i).1]
      rw [← hsum] at hlt
      have hlt' := ENNReal.ofReal_lt_ofReal_iff'.1 hlt
      refine ⟨wordPrefix x M, ⟨List.ofFn r, by simp, by exact_mod_cast hlt'.1,
        by exact_mod_cast hlt'.2, fun k hk ↦ ?_⟩, mem_listCylinder_wordPrefix x M⟩
      simp only [List.length_ofFn] at hk
      have hget : (List.ofFn r).get ⟨k, by simpa using hk⟩ = r ⟨k, hk⟩ := by simp
      simp only [hget]
      rcases hU ⟨k, hk⟩ with h0 | ⟨hE', hxu⟩
      · exact Or.inl h0.le
      · refine Or.inr ⟨U ⟨k, hk⟩, hE', ?_⟩
        have hle : (U ⟨k, hk⟩).length ≤ M :=
          Finset.le_sup (f := fun i ↦ (U i).length) (Finset.mem_univ _)
        rw [take_wordPrefix x hle, ← mem_listCylinder_iff_wordPrefix]
        exact hxu
    · rintro ⟨w, ⟨qs, hlen, hq, hpos, hall⟩, hxw⟩
      have hle : ∀ k (h : k < qs.length), ENNReal.ofReal (qs.get ⟨k, h⟩) ≤ f k x := by
        intro k h
        rcases hall k h with h0 | ⟨u, hu, htake⟩
        · rw [ENNReal.ofReal_of_nonpos (by exact_mod_cast h0)]
          exact zero_le
        · exact ((hfE k _ x).2 ⟨u, hu, mem_listCylinder_of_take_eq hxw htake⟩).le
      calc ENNReal.ofReal q < ENNReal.ofReal (qs.sum : ℝ) :=
            (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hpos)).2 (by exact_mod_cast hq)
        _ ≤ ∑ k ∈ Finset.range qs.length, f k x := hb_ofReal_listSum_le qs _ hle
        _ = ∑ k ∈ Finset.range n, f k x := by rw [hlen]

/-- Birkhoff averages of a lower semicomputable function are lower semicomputable, uniformly in
the length. Blueprint node `erg:hoyrup`. -/
theorem IsLscFunIn.shiftAverage {A : Set ℕ} {v : (ℕ → Bool) → ℝ≥0∞} (hv : IsLscFunIn A v) :
    IsLscFunFamilyIn A fun n : ℕ ↦ shiftAverage v n := by
  obtain ⟨E, hE, hEq⟩ := hv.comp_shiftMap_iterate.sum_range
  classical
  refine ⟨fun p ↦ 0 < p.1.1 ∧ E ((p.1.1, p.1.2 * p.1.1), p.2), ?_, fun n q ↦ ?_⟩
  · have h1 : IsREIn A fun p : (ℕ × ℚ) × List Bool ↦ 0 < p.1.1 :=
      isREIn_of_computable_decide (Primrec.nat_lt.comp (Primrec.const 0)
        (Primrec.fst.comp Primrec.fst)).decide.to_comp
    have h2 : IsREIn A fun p : (ℕ × ℚ) × List Bool ↦ E ((p.1.1, p.1.2 * p.1.1), p.2) :=
      hE.comp (((Computable.fst.comp Computable.fst).pair
        (computable₂_ratMul.comp (Computable.snd.comp Computable.fst)
          (computable_nat_to_rat.comp (Computable.fst.comp Computable.fst)))).pair
        Computable.snd).computableIn
    exact h1.and h2
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext x
      simp [Kolmogorov.PointToSet.shiftAverage]
    · have key : ∀ x, ENNReal.ofReal q < Kolmogorov.PointToSet.shiftAverage v n x ↔
          ENNReal.ofReal ((q * n : ℚ) : ℝ) < ∑ k ∈ Finset.range n, v (shiftMap^[k] x) := by
        intro x
        rw [Kolmogorov.PointToSet.shiftAverage, ENNReal.lt_div_iff_mul_lt
          (Or.inl (Nat.cast_ne_zero.2 hn.ne')) (Or.inl (ENNReal.natCast_ne_top n))]
        rw [Rat.cast_mul, Rat.cast_natCast, ENNReal.ofReal_mul' (Nat.cast_nonneg n),
          ENNReal.ofReal_natCast]
      have hE' := hEq n (q * n)
      ext x
      rw [mem_ofPred_eq, key, hb_mem_biUnion]
      have hx := (Set.ext_iff.1 hE' x).trans hb_mem_biUnion
      rw [mem_ofPred_eq] at hx
      beta_reduce at hx
      rw [hx]
      simp [hn]

/-- A lower semicomputable function is measurable. Blueprint node `erg:hoyrup`. -/
theorem IsLscFunIn.measurable {A : Set ℕ} {v : (ℕ → Bool) → ℝ≥0∞} (hv : IsLscFunIn A v) :
    Measurable v := by
  obtain ⟨E, -, hEq⟩ := hv
  refine measurable_of_Ioi fun a ↦ ?_
  have : v ⁻¹' Ioi a = ⋃ (q : ℚ) (_ : a < ENNReal.ofReal q), {x | ENNReal.ofReal q < v x} := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · intro h
      obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
      exact ⟨q, h1, h2⟩
    · rintro ⟨q, h1, h2⟩
      exact h1.trans h2
  rw [this]
  refine MeasurableSet.iUnion fun q ↦ MeasurableSet.iUnion fun _ ↦ ?_
  rw [hEq () q]
  exact MeasurableSet.biUnion (Set.to_countable _) fun w _ ↦ measurableSet_listCylinder w

/-- Rational cuts of a truncated subtraction `c - min(a, c)` in terms of cuts of `a`. -/
private lemma hb_lt_natCast_sub_min_iff (a : ℝ≥0∞) (c : ℕ) (q : ℚ) :
    ENNReal.ofReal q < (c : ℝ≥0∞) - min a c ↔
      (q ≤ 0 ∧ (0 : ℚ) < c ∧ a < ENNReal.ofReal ((c : ℚ) : ℝ)) ∨
        (0 < q ∧ q < c ∧ a < ENNReal.ofReal (((c : ℚ) - q : ℚ) : ℝ)) := by
  have hc : ENNReal.ofReal ((c : ℚ) : ℝ) = c := by simp
  rcases le_or_gt (c : ℝ≥0∞) a with hca | hac
  · rw [min_eq_right hca, tsub_self, hc]
    simp only [ENNReal.not_lt_zero, false_iff, not_or, not_and]
    refine ⟨fun _ _ h ↦ absurd (hca.trans_lt h) (lt_irrefl _), fun hq _ h ↦ ?_⟩
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have : ENNReal.ofReal (((c : ℚ) - q : ℚ) : ℝ) ≤ c := by
      rw [← hc]
      exact ENNReal.ofReal_le_ofReal (by push_cast; linarith)
    exact absurd (hca.trans_lt (h.trans_le this)) (lt_irrefl _)
  · have ha : a ≠ ⊤ := ne_top_of_lt hac
    rw [min_eq_left hac.le]
    have has : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    have hs0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    have hsc : a.toReal < c := by
      have := hac
      rw [has, ← ENNReal.ofReal_natCast] at this
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1
    rw [has, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_sub _ hs0, ENNReal.ofReal_lt_ofReal_iff',
      ENNReal.ofReal_lt_ofReal_iff', ENNReal.ofReal_lt_ofReal_iff']
    push_cast
    have e1 : q ≤ 0 ↔ (q : ℝ) ≤ 0 := by norm_cast
    have e2 : (0 : ℚ) < c ↔ (0 : ℝ) < c := by norm_cast
    have e3 : 0 < q ↔ (0 : ℝ) < q := by norm_cast
    have e4 : q < c ↔ (q : ℝ) < c := by norm_cast
    rw [e1, e2, e3, e4]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hq : (q : ℝ) ≤ 0
      · exact Or.inl ⟨hq, by linarith, by linarith, by linarith⟩
      · exact Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩

/-- Truncated subtraction `c - min(f, c)` of a function whose strict sublevel sets
`{f < r}`, `r` rational, are unions of cylinders over an `A`-r.e. set of words (uniformly) is
lower semicomputable. Blueprint node `erg:hoyrup`. -/
theorem isLscFunFamilyIn_natCast_sub_min {ι : Type*} [Primcodable ι] {A : Set ℕ}
    {f : ι → (ℕ → Bool) → ℝ≥0∞} (c : ℕ)
    (hf : ∃ E : (ι × ℚ) × List Bool → Prop, IsREIn A E ∧
      ∀ i (r : ℚ), {x | f i x < ENNReal.ofReal r} = ⋃ w ∈ {w | E ((i, r), w)}, listCylinder w) :
    IsLscFunFamilyIn A fun i x ↦ (c : ℝ≥0∞) - min (f i x) c := by
  obtain ⟨E, hE, hEq⟩ := hf
  classical
  refine ⟨fun p ↦ (p.1.2 ≤ 0 ∧ (0 : ℚ) < c ∧ E ((p.1.1, (c : ℚ)), p.2)) ∨
      (0 < p.1.2 ∧ p.1.2 < c ∧ E ((p.1.1, (c : ℚ) - p.1.2), p.2)), ?_, fun i q ↦ ?_⟩
  · have h1 : IsREIn A fun p : (ι × ℚ) × List Bool ↦ p.1.2 ≤ 0 :=
      isREIn_of_computable_decide (ComputableReals.primrec_ratLe.comp
        (Primrec.snd.comp Primrec.fst) (Primrec.const 0)).decide.to_comp
    have h2 : IsREIn A fun _ : (ι × ℚ) × List Bool ↦ (0 : ℚ) < c :=
      isREIn_of_computable_decide (Computable.const _)
    have h3 : IsREIn A fun p : (ι × ℚ) × List Bool ↦ E ((p.1.1, (c : ℚ)), p.2) :=
      hE.comp (((Computable.fst.comp Computable.fst).pair (Computable.const _)).pair
        Computable.snd).computableIn
    have h4 : IsREIn A fun p : (ι × ℚ) × List Bool ↦ 0 < p.1.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (Computable.snd.comp Computable.fst))
    have h5 : IsREIn A fun p : (ι × ℚ) × List Bool ↦ p.1.2 < c :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.snd.comp Computable.fst)
        (Computable.const _))
    have h6 : IsREIn A fun p : (ι × ℚ) × List Bool ↦ E ((p.1.1, (c : ℚ) - p.1.2), p.2) :=
      hE.comp (((Computable.fst.comp Computable.fst).pair (computable₂_ratSub.comp
        (Computable.const _) (Computable.snd.comp Computable.fst))).pair
        Computable.snd).computableIn
    exact (h1.and (h2.and h3)).or (h4.and (h5.and h6))
  · have hfE : ∀ (r : ℚ) y, f i y < ENNReal.ofReal r ↔ ∃ w, E ((i, r), w) ∧ y ∈ listCylinder w :=
      fun r y ↦ (Set.ext_iff.1 (hEq i r) y).trans hb_mem_biUnion
    ext x
    rw [mem_ofPred_eq, hb_lt_natCast_sub_min_iff, hfE, hfE, hb_mem_biUnion]
    constructor
    · rintro (⟨h1, h2, w, hw, hx⟩ | ⟨h1, h2, w, hw, hx⟩)
      · exact ⟨w, Or.inl ⟨h1, h2, hw⟩, hx⟩
      · exact ⟨w, Or.inr ⟨h1, h2, hw⟩, hx⟩
    · rintro ⟨w, (⟨h1, h2, hw⟩ | ⟨h1, h2, hw⟩), hx⟩
      · exact Or.inl ⟨h1, h2, w, hw, hx⟩
      · exact Or.inr ⟨h1, h2, w, hw, hx⟩

/-! ### Randomness: the Levin–Schnorr test -/

/-- The Levin–Schnorr test relation: `ν[w] < 2^{-c-m}` for some `c > K^A(w) - 1`, i.e.
`ν[w] < 2^{-K^A(w)-m}`. -/
private def hbLSRel (A : Set ℕ) (ν : Measure (ℕ → Bool)) (p : ℕ × List Bool) : Prop :=
  ∃ c : ℕ, (oracleNatComplexity A (Encodable.encode p.2) : ℝ) < (((c + 1 : ℕ) : ℚ) : ℝ) ∧
    (ν (listCylinder p.2)).toReal < (((2 ^ (c + p.1) : ℚ)⁻¹ : ℚ) : ℝ)

/-- The real value of `2⁻¹ ^ k ∈ [0, ∞]` is the rational `(2 ^ k)⁻¹`. -/
lemma toReal_two_inv_pow (k : ℕ) :
    ((2 : ℝ≥0∞)⁻¹ ^ k).toReal = (((2 ^ k : ℚ)⁻¹ : ℚ) : ℝ) := by
  simp [ENNReal.toReal_pow, ENNReal.toReal_inv, inv_pow]

/-- The Levin–Schnorr relation is `A`-r.e. -/
private lemma hb_isREIn_LSRel {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    (hc : IsComputableWordMeasureIn A ν) : IsREIn A (hbLSRel A ν) := by
  have h1 : IsREIn A fun z : (ℕ × List Bool) × ℕ ↦
      (oracleNatComplexity A (Encodable.encode z.1.2) : ℝ) < (((z.2 + 1 : ℕ) : ℚ) : ℝ) :=
    (isREIn_oracleNatComplexity_lt A).comp
      (f := fun z : (ℕ × List Bool) × ℕ ↦ (Encodable.encode z.1.2, ((z.2 + 1 : ℕ) : ℚ)))
      ((Computable.encode.comp (Computable.snd.comp Computable.fst)).pair
        (computable_nat_to_rat.comp
          (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).to_comp)).computableIn
  have h2 : IsREIn A fun z : (ℕ × List Bool) × ℕ ↦
      (ν (listCylinder z.1.2)).toReal < (((2 ^ (z.2 + z.1.1) : ℚ)⁻¹ : ℚ) : ℝ) :=
    (birkhoff_computableIn_lt A _ hc).comp
      (f := fun z : (ℕ × List Bool) × ℕ ↦ (z.1.2, ((2 ^ (z.2 + z.1.1) : ℚ)⁻¹ : ℚ)))
      ((Computable.snd.comp Computable.fst).pair
      (computable_rat_inv_two_pow.comp (Primrec.nat_add.comp Primrec.snd
        (Primrec.fst.comp Primrec.fst)).to_comp)).computableIn
  exact (h1.and h2).exists

/-- The Levin–Schnorr test has level measures at most `2^{-m}` (Kraft's inequality). -/
private lemma hb_measure_LSTest_le {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (m : ℕ) :
    ν (⋃ w ∈ {w | hbLSRel A ν (m, w)}, listCylinder w) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
  have hterm : ∀ w : List Bool, ν (⋃ (_ : w ∈ {w | hbLSRel A ν (m, w)}), listCylinder w) ≤
      (2 : ℝ≥0∞)⁻¹ ^ m * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A (Encodable.encode w) := by
    intro w
    by_cases hw : hbLSRel A ν (m, w)
    · obtain ⟨c, hK, hν⟩ := hw
      have hw' : hbLSRel A ν (m, w) := ⟨c, hK, hν⟩
      simp only [mem_ofPred_eq, hw', iUnion_true]
      have hK' : oracleNatComplexity A (Encodable.encode w) ≤ c := by
        have : (oracleNatComplexity A (Encodable.encode w) : ℝ) < c + 1 := by
          exact_mod_cast hK
        exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
      rw [← toReal_two_inv_pow, ENNReal.toReal_lt_toReal (measure_ne_top _ _)
        (by simp)] at hν
      calc ν (listCylinder w) ≤ (2 : ℝ≥0∞)⁻¹ ^ (c + m) := hν.le
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (oracleNatComplexity A (Encodable.encode w) + m) :=
          pow_le_pow_right_of_le_one' (by norm_num) (by omega)
        _ = _ := by rw [pow_add, mul_comm]
    · simp [hw]
  calc ν (⋃ w ∈ {w | hbLSRel A ν (m, w)}, listCylinder w)
      ≤ ∑' w : List Bool, ν (⋃ (_ : w ∈ {w | hbLSRel A ν (m, w)}), listCylinder w) :=
        measure_iUnion_le _
    _ ≤ ∑' w : List Bool,
        (2 : ℝ≥0∞)⁻¹ ^ m * (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A (Encodable.encode w) :=
        ENNReal.tsum_le_tsum hterm
    _ = (2 : ℝ≥0∞)⁻¹ ^ m * ∑' w : List Bool,
        (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A (Encodable.encode w) := ENNReal.tsum_mul_left
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i :=
        by
          gcongr
          exact ENNReal.tsum_comp_le_tsum_of_injective Encodable.encode_injective
            (fun i ↦ (2 : ℝ≥0∞)⁻¹ ^ oracleNatComplexity A i)
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * 1 := by
          gcongr
          exact oracle_kraft A
    _ = _ := mul_one _

/-- At a `ν`-random sequence relative to `A`, `ν[ω↾n] ≥ 2^{-K^A(ω↾n)-m}` for some `m` and all
`n`. -/
private lemma hb_exists_two_inv_pow_le {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hc : IsComputableWordMeasureIn A ν) {ω : ℕ → Bool}
    (hω : ω ∈ wordRandomPoints A ν) :
    ∃ m : ℕ, ∀ n, (2 : ℝ≥0∞)⁻¹ ^ (wordComplexity A ω n + m) ≤
      ν (listCylinder (wordPrefix ω n)) := by
  obtain ⟨m, hm⟩ := hω (fun m ↦ ⋃ w ∈ {w | hbLSRel A ν (m, w)}, listCylinder w)
    ⟨hbLSRel A ν, hb_isREIn_LSRel hc, fun _ ↦ rfl, hb_measure_LSTest_le⟩
  refine ⟨m, fun n ↦ ?_⟩
  by_contra hlt
  replace hlt := not_le.1 hlt
  apply hm
  rw [hb_mem_biUnion]
  refine ⟨wordPrefix ω n, ⟨wordComplexity A ω n, ?_, ?_⟩, mem_listCylinder_wordPrefix ω n⟩
  · push_cast
    simp only [wordComplexity]
    linarith
  · rw [← toReal_two_inv_pow, ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by simp)]
    exact hlt

/-- A sequence that is `ν`-random relative to `A` meets no null cylinder.
Blueprint node `erg:hoyrup`. -/
theorem listCylinder_wordPrefix_pos_of_mem_wordRandomPoints {A : Set ℕ}
    {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν] (hc : IsComputableWordMeasureIn A ν)
    {ω : ℕ → Bool} (hω : ω ∈ wordRandomPoints A ν) (n : ℕ) :
    0 < ν (listCylinder (wordPrefix ω n)) := by
  obtain ⟨m, hm⟩ := hb_exists_two_inv_pow_le hc hω
  refine lt_of_lt_of_le ?_ (hm n)
  exact ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _

/-- The lower half of the Levin–Schnorr theorem, relativized: at a `ν`-random sequence,
`-log₂ ν[ω↾n] ≤ K^A(ω↾n) + c` for all `n`. Blueprint node `erg:hoyrup`. -/
theorem exists_infoBits_le_wordComplexity_add {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hc : IsComputableWordMeasureIn A ν) {ω : ℕ → Bool}
    (hω : ω ∈ wordRandomPoints A ν) :
    ∃ c : ℕ, ∀ n, infoBits (ν (listCylinder (wordPrefix ω n))) ≤ wordComplexity A ω n + c := by
  obtain ⟨m, hm⟩ := hb_exists_two_inv_pow_le hc hω
  refine ⟨m, fun n ↦ ?_⟩
  calc infoBits (ν (listCylinder (wordPrefix ω n)))
      ≤ infoBits ((2 : ℝ≥0∞)⁻¹ ^ (wordComplexity A ω n + m)) := infoBits_antitone (hm n)
    _ ≤ ((wordComplexity A ω n + m : ℕ) : ℝ≥0∞) := (infoBits_two_inv_pow _).le
    _ = _ := by push_cast; rfl

end Kolmogorov.PointToSet
