/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupPoincareAux

/-!
# Effective Poincaré recurrence on the binary shift

Theorem 3.1 of Hoyrup (STACS 2012), from Bienvenu–Day–Hoyrup–Mezhirov–Shen, *A constructive version
of Birkhoff's ergodic theorem for Martin-Löf random points* (arXiv:1007.5249), Theorem 7,
relativized: for an `A`-computable shift-invariant ergodic probability measure `ν` on `ℕ → Bool`
and an effectively closed set `C` (its complement `U` is a union of cylinders over an `A`-r.e. set
of words) with `ν(C) > 0`, every sequence that is `ν`-random relative to `A` has a tail in `C`.

Proof (BDHMS, Theorem 7). Fix rationals `ν(U) < s < r < 1`. For a cylinder `[u]` the search
predicate `good ν s r (u, n)` of `HoyrupPoincareAux` is `A`-r.e., halts on some `n` when
`ν[u] > 0` (mean ergodic theorem in `L¹` for `1_{[u]}` and Markov's inequality), and gives
`ν([u] ∩ ⋂_{i ≤ n} σ^{-i} U) ≤ r ν[u]` (`(n+1) ν([u] ∩ ⋂_{i≤n} σ^{-i} U)` is at most the average
`∑_{j ≤ n} ν(σ^{-j}[u] ∩ σ^{-n} U)`, by invariance). BDHMS's criterion
`∫ |a_n - ν[u]| < (r - s) ν[u]` is replaced by a count threshold, so that only finite sums of
cylinder measures are computed.

The iteration (`PoincareAux.level`): level `0` is the empty word, and the children of a word `J`
(`stepRel`) are the words `v ⊒ J` such that, for every prefix `J↾i` of `J` (including `J`),
some `n` with `good ν s r (J↾i, n)` has `σ^l [v] ⊆ U` for all `l ≤ n`; the children of `J` cover
`[J] ∩ trapAll J` (`biUnion_stepRel`). Levels are one r.e. predicate, through chains of children
(`chainOk`). No disjointification is needed: `trapAll` is antitone along prefixes, so the union
over a level is the union over its prefix-minimal words, whose cylinders are disjoint
(`measure_biUnion_inter_le`), and `ν(level k + 1) ≤ r ν(level k)`, hence `≤ r^k`
(`measure_level_le`). A sequence all of whose tails lie in `U` and whose prefixes have positive
measure lies in every level (`exists_level_mem`); null cylinders are excluded at random points
by `listCylinder_wordPrefix_pos_of_mem_wordRandomPoints`. The levels `c m` with `r^c ≤ 1/2`
form a test.

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

namespace PoincareAux

/-! ### Generic helpers -/

/-- Finitely many eventually-true monotone conditions hold together. -/
lemma exists_forall_lt_of_mono {P : ℕ → ℕ → Prop} (hmono : ∀ i m m', m ≤ m' → P i m → P i m')
    (N : ℕ) (h : ∀ i < N, ∃ m, P i m) : ∃ m, ∀ i < N, P i m := by
  induction N with
  | zero => exact ⟨0, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  | succ N ih =>
    obtain ⟨m₁, hm₁⟩ := ih fun i hi ↦ h i (by omega)
    obtain ⟨m₂, hm₂⟩ := h N (by omega)
    refine ⟨max m₁ m₂, fun i hi ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hmono i _ _ (le_max_left _ _) (hm₁ i hi)
    · exact hmono i _ _ (le_max_right _ _) hm₂

/-- Bounded universal quantification preserves relative enumerability. -/
lemma isREIn_forall_lt {α : Type*} [Primcodable α] {A : Set ℕ} {F : α × ℕ → Prop}
    (hF : IsREIn A F) : IsREIn A fun p : α × ℕ ↦ ∀ i < p.2, F (p.1, i) := by
  have h1 : IsREIn A fun z : α × ℕ × ℕ ↦ F (z.1, z.2.2) :=
    hF.comp (Computable.fst.pair (Computable.snd.comp Computable.snd)).computableIn
  have h2 := (IsREIn.list_forall_get h1).comp
    (f := fun p : α × ℕ ↦ (p.1, List.range p.2))
    (Computable.fst.pair (Primrec.list_range.to_comp.comp Computable.snd)).computableIn
  have heq : (fun p : α × ℕ ↦ ∀ k (h : k < (p.1, List.range p.2).2.length),
      F ((p.1, List.range p.2).1, ((p.1, List.range p.2).2.get ⟨k, h⟩))) =
      fun p : α × ℕ ↦ ∀ i < p.2, F (p.1, i) := by
    funext p
    simp
  rw [heq] at h2
  exact h2

/-- Prefix-minimal elements: every cylinder union is a disjoint cylinder union, and the measure of
`⋃_{J ∈ T} [J] ∩ H J` is at most `c ν(⋃_{J ∈ T} [J])` when `ν([J] ∩ H J) ≤ c ν[J]` and `H` is
antitone along prefixes. -/
lemma measure_biUnion_inter_le (ν : Measure (ℕ → Bool)) (T : Set (List Bool))
    (H : List Bool → Set (ℕ → Bool)) (c : ℝ≥0∞)
    (hH : ∀ J, ν (listCylinder J ∩ H J) ≤ c * ν (listCylinder J))
    (hanti : ∀ J J', J' <+: J → H J ⊆ H J') :
    ν (⋃ J ∈ T, listCylinder J ∩ H J) ≤ c * ν (⋃ J ∈ T, listCylinder J) := by
  set T' := {J | J ∈ T ∧ ∀ J' ∈ T, J' <+: J → J' = J} with hT'
  have hmin : ∀ n, ∀ J ∈ T, J.length = n → ∃ J' ∈ T', J' <+: J := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro J hJ hn
      by_cases hJ' : J ∈ T'
      · exact ⟨J, hJ', List.prefix_refl J⟩
      · simp only [hT', mem_ofPred_eq, not_and, not_forall] at hJ'
        obtain ⟨J', hJ'T, hpre, hne⟩ := hJ' hJ
        have hlt : J'.length < n := by
          rw [← hn]
          exact lt_of_le_of_ne hpre.length_le fun h ↦ hne (hpre.eq_of_length h)
        obtain ⟨J'', hJ'', hpre'⟩ := ih _ hlt J' hJ'T rfl
        exact ⟨J'', hJ'', hpre'.trans hpre⟩
  have hsub : (⋃ J ∈ T, listCylinder J ∩ H J) ⊆ ⋃ J ∈ T', listCylinder J ∩ H J := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨J, hJ, hxJ, hxH⟩ := hx
    obtain ⟨J', hJ', hpre⟩ := hmin _ J hJ rfl
    exact ⟨J', hJ', listCylinder_subset_of_prefix hpre hxJ, hanti J J' hpre hxH⟩
  have hdisj : T'.PairwiseDisjoint listCylinder := by
    intro J₁ h₁ J₂ h₂ hne
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
    rcases prefix_or_prefix_of_mem hx₁ hx₂ with h | h
    · exact h₂.2 J₁ h₁.1 h
    · exact (h₁.2 J₂ h₂.1 h).symm
  calc ν (⋃ J ∈ T, listCylinder J ∩ H J) ≤ ν (⋃ J ∈ T', listCylinder J ∩ H J) :=
        measure_mono hsub
    _ ≤ ∑' J : T', ν (listCylinder (J : List Bool) ∩ H J) :=
        measure_biUnion_le ν T'.to_countable _
    _ ≤ ∑' J : T', c * ν (listCylinder (J : List Bool)) := ENNReal.tsum_le_tsum fun J ↦ hH J
    _ = c * ν (⋃ J ∈ T', listCylinder J) := by
        rw [ENNReal.tsum_mul_left, measure_biUnion T'.to_countable hdisj
          fun J _ ↦ measurableSet_listCylinder J]
    _ ≤ c * ν (⋃ J ∈ T, listCylinder J) :=
        mul_le_mul_right (measure_mono (biUnion_subset_biUnion_left fun J (hJ : J ∈ T') ↦ hJ.1)) c

/-! ### One step of the construction -/

section step

variable (E : List Bool → Prop) (ν : Measure (ℕ → Bool)) (s r : ℚ)

/-- The children of a word `J`: the words `v` extending `J` such that, for every prefix `J↾i` of
`J`, some `n` with `good ν s r (J↾i, n)` has `σ^l [v] ⊆ U` for all `l ≤ n`, where
`U = ⋃_{E w} [w]`. -/
def stepRel (q : List Bool × List Bool) : Prop :=
  q.1 <+: q.2 ∧ ∀ i < q.1.length + 1, ∃ n, good ν s r (q.1.take i, n) ∧
    ∀ l < n + 1, ∃ w, E w ∧ w <+: q.2.drop l

/-- The set cut out of `[J]` by the children of `J`. -/
def trapAll (J : List Bool) : Set (ℕ → Bool) :=
  {x | ∀ i < J.length + 1, ∃ n, good ν s r (J.take i, n) ∧
    x ∈ trapSet (⋃ w ∈ {w | E w}, listCylinder w) n}

/-- `trapAll` is antitone along prefixes. -/
lemma trapAll_anti {J J' : List Bool} (h : J' <+: J) : trapAll E ν s r J ⊆ trapAll E ν s r J' := by
  intro x hx i hi
  have hl := h.length_le
  obtain ⟨n, hn, hx⟩ := hx i (by omega)
  refine ⟨n, ?_, hx⟩
  rwa [List.prefix_iff_eq_take.mp h, List.take_take, min_eq_left (by omega)]

/-- The children of `J` cover exactly `[J] ∩ trapAll J`. -/
lemma biUnion_stepRel (J : List Bool) :
    ⋃ v ∈ {v | stepRel E ν s r (J, v)}, listCylinder v = listCylinder J ∩ trapAll E ν s r J := by
  ext x
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop, mem_inter_iff]
  constructor
  · rintro ⟨v, ⟨hJv, hv⟩, hx⟩
    refine ⟨listCylinder_subset_of_prefix hJv hx, fun i hi ↦ ?_⟩
    obtain ⟨n, hn, hl⟩ := hv i hi
    refine ⟨n, hn, fun l hl' ↦ ?_⟩
    obtain ⟨w, hw, hpre⟩ := hl l (Nat.lt_succ_of_le hl')
    rw [mem_listCylinder_iff] at hx
    rw [← hx, prefix_drop_wordPrefix_iff] at hpre
    exact mem_biUnion (x := w) hw hpre.2
  · rintro ⟨hxJ, hx⟩
    -- the conditions on a prefix `x↾m`, monotone in `m`
    have hmono_w : ∀ (w : List Bool) (l m m' : ℕ), m ≤ m' →
        w <+: (wordPrefix x m).drop l → w <+: (wordPrefix x m').drop l := by
      intro w l m m' hm h
      rw [prefix_drop_wordPrefix_iff] at h ⊢
      exact ⟨by omega, h.2⟩
    have hQ : ∀ i < J.length + 1, ∃ m, ∃ n, good ν s r (J.take i, n) ∧
        ∀ l < n + 1, ∃ w, E w ∧ w <+: (wordPrefix x m).drop l := by
      intro i hi
      obtain ⟨n, hn, hxn⟩ := hx i hi
      have hP : ∀ l < n + 1, ∃ m, ∃ w, E w ∧ w <+: (wordPrefix x m).drop l := by
        intro l hl
        have hU := hxn l (Nat.lt_succ_iff.mp hl)
        simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hU
        obtain ⟨w, hw, hxw⟩ := hU
        exact ⟨w.length + l, w, hw, prefix_drop_wordPrefix_iff.mpr ⟨by omega, hxw⟩⟩
      obtain ⟨m, hm⟩ := exists_forall_lt_of_mono
        (fun l m m' hmm' ⟨w, hw, h⟩ ↦ ⟨w, hw, hmono_w w l m m' hmm' h⟩) (n + 1) hP
      exact ⟨m, n, hn, hm⟩
    obtain ⟨m, hm⟩ := exists_forall_lt_of_mono
      (fun i m m' hmm' ⟨n, hn, h⟩ ↦ ⟨n, hn, fun l hl ↦
        let ⟨w, hw, hp⟩ := h l hl
        ⟨w, hw, hmono_w w l m m' hmm' hp⟩⟩) (J.length + 1) hQ
    refine ⟨wordPrefix x (max m J.length), ⟨?_, fun i hi ↦ ?_⟩, mem_listCylinder_wordPrefix _ _⟩
    · exact prefix_wordPrefix_iff.mpr ⟨le_max_right _ _, hxJ⟩
    · obtain ⟨n, hn, h⟩ := hm i hi
      exact ⟨n, hn, fun l hl ↦
        let ⟨w, hw, hp⟩ := h l hl
        ⟨w, hw, hmono_w w l m _ (le_max_left _ _) hp⟩⟩

/-- The set cut out by the children of `J` has measure at most `r ν[J]`. -/
lemma measure_trapAll_le [IsProbabilityMeasure ν] (hσ : MeasurePreserving shiftMap ν ν)
    (hr : 0 < r) (hUs : ν.real (⋃ w ∈ {w | E w}, listCylinder w) ≤ s) (J : List Bool) :
    ν (listCylinder J ∩ trapAll E ν s r J) ≤ ENNReal.ofReal r * ν (listCylinder J) := by
  classical
  by_cases hex : ∃ n, good ν s r (J, n)
  · have hsub : listCylinder J ∩ trapAll E ν s r J ⊆
        listCylinder J ∩ trapSet (⋃ w ∈ {w | E w}, listCylinder w) (Nat.find hex) := by
      rintro x ⟨hxJ, hx⟩
      obtain ⟨n, hn, hxn⟩ := hx J.length (Nat.lt_succ_self _)
      rw [List.take_length] at hn
      exact ⟨hxJ, trapSet_anti _ (Nat.find_min' hex hn) hxn⟩
    exact (measure_mono hsub).trans (measure_trap_le_of_good hσ
      (measurableSet_biUnion_listCylinder _) hr hUs (Nat.find_spec hex))
  · have hempty : listCylinder J ∩ trapAll E ν s r J = ∅ := by
      refine eq_empty_of_forall_notMem fun x ⟨_, hx⟩ ↦ hex ?_
      obtain ⟨n, hn, _⟩ := hx J.length (Nat.lt_succ_self _)
      rw [List.take_length] at hn
      exact ⟨n, hn⟩
    rw [hempty, measure_empty]
    exact bot_le

/-! ### Levels: chains of children -/

/-- A chain `c = [J_k, …, J_1]` (newest first): each `J_{i+1}` is a child of `J_i`, and `J_1` is
a child of the empty word. -/
def chainOk (c : List (List Bool)) : Prop :=
  ∀ i < c.length, stepRel E ν s r (c.getD (i + 1) [], c.getD i [])

/-- The words of level `k`: the last words of the chains of length `k` (the empty word for
`k = 0`). -/
def level (q : ℕ × List Bool) : Prop :=
  ∃ c : List (List Bool), (c.length = q.1 ∧ c.getD 0 [] = q.2) ∧ chainOk E ν s r c

/-- Level `0` is the empty word. -/
lemma level_zero (v : List Bool) : level E ν s r (0, v) ↔ v = [] := by
  constructor
  · rintro ⟨c, ⟨hc, hv⟩, -⟩
    rw [List.length_eq_zero_iff] at hc
    subst hc
    simpa using hv.symm
  · rintro rfl
    exact ⟨[], ⟨rfl, rfl⟩, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

/-- Level `k + 1` consists of the children of level `k`. -/
lemma level_succ (k : ℕ) (v : List Bool) :
    level E ν s r (k + 1, v) ↔ ∃ J, level E ν s r (k, J) ∧ stepRel E ν s r (J, v) := by
  constructor
  · rintro ⟨c, ⟨hc, hv⟩, hok⟩
    cases c with
    | nil => simp at hc
    | cons v' c' =>
      simp only [List.length_cons, add_left_inj, List.getD_cons_zero] at hc hv
      subst hv
      refine ⟨c'.getD 0 [], ⟨c', ⟨hc, rfl⟩, fun i hi ↦ ?_⟩, ?_⟩
      · have := hok (i + 1) (by simp; omega)
        simpa only [List.getD_cons_succ] using this
      · have := hok 0 (by simp)
        simpa only [List.getD_cons_succ, List.getD_cons_zero] using this
  · rintro ⟨J, ⟨c', ⟨hc, hJ⟩, hok⟩, hstep⟩
    refine ⟨v :: c', ⟨by simp [hc], rfl⟩, fun i hi ↦ ?_⟩
    cases i with
    | zero => simpa only [List.getD_cons_succ, List.getD_cons_zero, hJ] using hstep
    | succ i =>
      simp only [List.getD_cons_succ]
      exact hok i (by simp at hi; omega)

end step

/-! ### Effectivity of the construction -/

section effective

variable {A : Set ℕ} {E : List Bool → Prop} {ν : Measure (ℕ → Bool)}

/-- The prefix relation on words is decidable by a primitive recursive test. -/
lemma isREIn_prefix_drop :
    IsREIn A fun z : (List Bool × ℕ) × List Bool ↦ z.2 <+: z.1.1.drop z.1.2 := by
  have h : IsREIn A fun z : (List Bool × ℕ) × List Bool ↦
      (z.1.1.drop z.1.2).take z.2.length = z.2 :=
    isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_take.comp
      (Primrec.list_length.comp Primrec.snd) (Primrec.list_drop.comp
        (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))) Primrec.snd).decide.to_comp
  convert h using 1
  funext z
  exact propext (List.prefix_iff_eq_take.trans eq_comm)

/-- "Some word of `E` occurs in `v` at position `l`" is `A`-r.e. -/
lemma isREIn_coveredAt (hE : IsREIn A E) :
    IsREIn A fun p : List Bool × ℕ ↦ ∃ w, E w ∧ w <+: p.1.drop p.2 :=
  ((hE.comp Computable.snd.computableIn).and isREIn_prefix_drop).exists

/-- The child relation is `A`-r.e. -/
lemma isREIn_stepRel (hE : IsREIn A E) (hc : IsComputableWordMeasureIn A ν) (s r : ℚ) :
    IsREIn A (stepRel E ν s r) := by
  have R2 : IsREIn A fun p : List Bool × ℕ ↦ ∀ l < p.2 + 1, ∃ w, E w ∧ w <+: p.1.drop l :=
    (isREIn_forall_lt (isREIn_coveredAt hE)).comp (f := fun p : List Bool × ℕ ↦ (p.1, p.2 + 1))
      (Computable.fst.pair (Primrec.succ.to_comp.comp Computable.snd)).computableIn
  have R3 : IsREIn A fun z : (List Bool × List Bool) × ℕ ↦
      ∃ n, good ν s r (z.1.1.take z.2, n) ∧ ∀ l < n + 1, ∃ w, E w ∧ w <+: z.1.2.drop l :=
    (((isREIn_good hc s r).comp
      (f := fun y : ((List Bool × List Bool) × ℕ) × ℕ ↦ (y.1.1.1.take y.1.2, y.2))
      ((Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
          Primrec.snd).to_comp.computableIn).and
      (R2.comp (f := fun y : ((List Bool × List Bool) × ℕ) × ℕ ↦ (y.1.1.2, y.2))
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
          Computable.snd).computableIn)).exists
  have R4 : IsREIn A fun q : List Bool × List Bool ↦ ∀ i < q.1.length + 1,
      ∃ n, good ν s r (q.1.take i, n) ∧ ∀ l < n + 1, ∃ w, E w ∧ w <+: q.2.drop l :=
    (isREIn_forall_lt R3).comp (f := fun q : List Bool × List Bool ↦ (q, q.1.length + 1))
      (Computable.id.pair (Primrec.succ.to_comp.comp
        (Primrec.list_length.to_comp.comp Computable.fst))).computableIn
  have R1 : IsREIn A fun q : List Bool × List Bool ↦ q.1 <+: q.2 :=
    isREIn_prefix_drop.comp (f := fun q : List Bool × List Bool ↦ ((q.2, 0), q.1))
      ((Computable.snd.pair (Computable.const 0)).pair Computable.fst).computableIn
  exact R1.and R4

/-- The levels form an `A`-r.e. relation. -/
lemma isREIn_level (hE : IsREIn A E) (hc : IsComputableWordMeasureIn A ν) (s r : ℚ) :
    IsREIn A (level E ν s r) := by
  have hF : IsREIn A fun p : List (List Bool) × ℕ ↦
      stepRel E ν s r (p.1.getD (p.2 + 1) [], p.1.getD p.2 []) :=
    (isREIn_stepRel hE hc s r).comp
      (f := fun p : List (List Bool) × ℕ ↦ (p.1.getD (p.2 + 1) [], p.1.getD p.2 []))
      ((((Primrec.list_getD []).comp Primrec.fst (Primrec.succ.comp Primrec.snd)).pair
        ((Primrec.list_getD []).comp Primrec.fst Primrec.snd)).to_comp.computableIn)
  have hchain : IsREIn A (chainOk E ν s r) :=
    (isREIn_forall_lt hF).comp (f := fun c : List (List Bool) ↦ (c, c.length))
      (Computable.id.pair Primrec.list_length.to_comp).computableIn
  have h1 : IsREIn A fun z : (ℕ × List Bool) × List (List Bool) ↦ z.2.length = z.1.1 :=
    isREIn_of_computable_decide
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)).decide.to_comp
  have h2 : IsREIn A fun z : (ℕ × List Bool) × List (List Bool) ↦ z.2.getD 0 [] = z.1.2 :=
    isREIn_of_computable_decide
      (Primrec.eq.comp ((Primrec.list_getD []).comp Primrec.snd (Primrec.const 0))
        (Primrec.snd.comp Primrec.fst)).decide.to_comp
  exact ((h1.and h2).and (hchain.comp Computable.snd.computableIn)).exists

end effective

/-! ### Measure and covering of the levels -/

section levels

variable {E : List Bool → Prop} {ν : Measure (ℕ → Bool)} [IsProbabilityMeasure ν] {s r : ℚ}

/-- The level-`k` cylinders have measure at most `r^k`. -/
lemma measure_level_le (hσ : MeasurePreserving shiftMap ν ν) (hr : 0 < r)
    (hUs : ν.real (⋃ w ∈ {w | E w}, listCylinder w) ≤ s) (k : ℕ) :
    ν (⋃ v ∈ {v | level E ν s r (k, v)}, listCylinder v) ≤ ENNReal.ofReal r ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    have heq : (⋃ v ∈ {v | level E ν s r (k + 1, v)}, listCylinder v) =
        ⋃ J ∈ {J | level E ν s r (k, J)}, listCylinder J ∩ trapAll E ν s r J := by
      ext x
      simp only [mem_iUnion, mem_ofPred_eq, exists_prop, level_succ]
      constructor
      · rintro ⟨v, ⟨J, hJ, hJv⟩, hx⟩
        refine ⟨J, hJ, ?_⟩
        rw [← biUnion_stepRel]
        exact mem_biUnion (x := v) hJv hx
      · rintro ⟨J, hJ, hx⟩
        rw [← biUnion_stepRel] at hx
        simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hx
        obtain ⟨v, hv, hxv⟩ := hx
        exact ⟨v, ⟨J, hJ, hv⟩, hxv⟩
    rw [heq, pow_succ']
    exact (measure_biUnion_inter_le ν _ _ _ (measure_trapAll_le E ν s r hσ hr hUs)
      fun J J' h ↦ trapAll_anti E ν s r h).trans (mul_le_mul_right ih _)

/-- A sequence with positive prefixes all of whose tails lie in `U` lies in every level. -/
lemma exists_level_mem (hν : Ergodic shiftMap ν) (hs0 : 0 ≤ s) (hsr : s < r) (hr1 : r ≤ 1)
    {ω : ℕ → Bool} (hpos : ∀ n, 0 < ν (listCylinder (wordPrefix ω n)))
    (hU : ∀ n, shiftMap^[n] ω ∈ ⋃ w ∈ {w | E w}, listCylinder w) (k : ℕ) :
    ∃ v, level E ν s r (k, v) ∧ ω ∈ listCylinder v := by
  induction k with
  | zero => exact ⟨[], (level_zero E ν s r []).mpr rfl, fun i hi ↦ absurd hi (by simp)⟩
  | succ k ih =>
    obtain ⟨J, hJ, hωJ⟩ := ih
    have hmem : ω ∈ listCylinder J ∩ trapAll E ν s r J := by
      refine ⟨hωJ, fun i _ ↦ ?_⟩
      have hωi : ω ∈ listCylinder (J.take i) :=
        listCylinder_subset_of_prefix (List.take_prefix _ _) hωJ
      have hp : 0 < ν (listCylinder (J.take i)) := by
        rw [mem_listCylinder_iff] at hωi
        rw [← hωi]
        exact hpos _
      obtain ⟨n, hn⟩ := exists_good hν hs0 hsr hr1 hp
      exact ⟨n, hn, fun l _ ↦ hU l⟩
    rw [← biUnion_stepRel] at hmem
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop] at hmem
    obtain ⟨v, hv, hωv⟩ := hmem
    exact ⟨v, (level_succ E ν s r k v).mpr ⟨J, hJ, hv⟩, hωv⟩

end levels

end PoincareAux

/-- Effective Poincaré recurrence: a sequence that is `ν`-random relative to `A` has a tail in every
effectively closed set of positive measure. Blueprint node `erg:hoyrup`. -/
theorem exists_iterate_notMem_of_mem_wordRandomPoints {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν) (hc : IsComputableWordMeasureIn A ν)
    {E : List Bool → Prop} (hE : IsREIn A E)
    (hpos : 0 < ν (⋃ w ∈ {w | E w}, listCylinder w)ᶜ) {ω : ℕ → Bool}
    (hω : ω ∈ wordRandomPoints A ν) :
    ∃ n, shiftMap^[n] ω ∉ ⋃ w ∈ {w | E w}, listCylinder w := by
  set U := ⋃ w ∈ {w | E w}, listCylinder w
  have hUm : MeasurableSet U := PoincareAux.measurableSet_biUnion_listCylinder _
  by_contra hcon
  push Not at hcon
  -- rationals `ν(U) < s < r < 1`
  have hU1 : ν.real U < 1 := by
    have h1 : ν U < 1 := by
      rw [prob_compl_eq_one_sub hUm] at hpos
      exact tsub_pos_iff_lt.mp hpos
    rw [measureReal_def, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr h1
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn hU1
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hs2
  have hs0 : (0 : ℚ) ≤ s := by exact_mod_cast measureReal_nonneg.trans hs1.le
  have hsr : s < r := by exact_mod_cast hr1
  have hr0 : 0 < r := lt_of_le_of_lt hs0 hsr
  have hr1' : r ≤ 1 := by exact_mod_cast hr2.le
  obtain ⟨c, hcr⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hr2
  -- the test `V m = ⋃ {[v] | v of level c m}`
  set V : ℕ → Set (ℕ → Bool) :=
    fun m ↦ ⋃ v ∈ {v | PoincareAux.level E ν s r (c * m, v)}, listCylinder v
  have hV : IsWordTestIn A ν V := by
    refine ⟨fun q ↦ PoincareAux.level E ν s r (c * q.1, q.2), ?_, fun m ↦ rfl, fun m ↦ ?_⟩
    · exact (PoincareAux.isREIn_level hE hc s r).comp
        (f := fun q : ℕ × List Bool ↦ (c * q.1, q.2))
        ((Primrec.nat_mul.comp (Primrec.const c) Primrec.fst).pair
          Primrec.snd).to_comp.computableIn
    · calc ν (V m) ≤ ENNReal.ofReal r ^ (c * m) :=
            PoincareAux.measure_level_le hν.toMeasurePreserving hr0 hs1.le (c * m)
        _ = ENNReal.ofReal ((r : ℝ) ^ c) ^ m := by
            rw [pow_mul, ENNReal.ofReal_pow (by exact_mod_cast hr0.le)]
        _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
            gcongr
            calc ENNReal.ofReal ((r : ℝ) ^ c) ≤ ENNReal.ofReal (1 / 2) :=
                  ENNReal.ofReal_le_ofReal hcr.le
              _ = 2⁻¹ := by
                  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
                  simp
  obtain ⟨m, hm⟩ := hω V hV
  obtain ⟨v, hv, hωv⟩ := PoincareAux.exists_level_mem hν hs0 hsr hr1'
    (fun n ↦ listCylinder_wordPrefix_pos_of_mem_wordRandomPoints hc hω n) hcon (c * m)
  exact hm (mem_biUnion (x := v) hv hωv)

end Kolmogorov.PointToSet
