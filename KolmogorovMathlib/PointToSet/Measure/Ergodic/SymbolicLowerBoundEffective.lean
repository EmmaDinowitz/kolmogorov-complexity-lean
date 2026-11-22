/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.SymbolicLowerBoundAux


/-!
# Binary suffices in (I3): computability, randomness and complexity of the coded sequence

Auxiliary material for `SymbolicLowerBound`, continuing `SymbolicLowerBoundAux` (the one-hot
block code `C = blockCode p`, `ν' = blockPush ν`, `ν'' = blockAvg ν`).

* `isComputableRealFamilyIn_listSum`: a constant `c` (`|c| ≤ 1`) times the sum of an
  `A`-computable real family over a computable list of indices is an `A`-computable real family
  (the library has no closure of `IsComputableRealFamilyIn` under finite sums);
  `computableIn_list_map` maps a relatively computable function over a list.
* `isComputableWordMeasureIn_blockAvg`: `ν''` is `A`-computable on cylinders when `ν` is, through
  `blockAvg_listCylinder_toReal`: `ν''[v] = (1/p) ∑_{u ∈ wordList p v} ν[u]`, where `wordList p v`
  lists, for each shift `j < p`, the words `u` of length `|v| + 1` whose code carries `v` at
  position `j` (`condW`, `allWords`).
* `blockCode_mem_wordRandomPoints`: if `ω` is `ν`-random relative to `A`, then `C(ω)` is
  `ν''`-random relative to `A`: the pull-back of a cylinder test for `ν''` under `C` (with the
  index shifted by `p`) is a cylinder test for `ν` (`preimage_blockCode_iUnion`), since
  `ν(C⁻¹ s) ≤ p ν''(s) ≤ 2^p ν''(s)`.
* `exists_wordComplexity_blockCode_le`: `K^A(C(ω)↾pn) ≤ K^A(ω↾n) + O(1)`, since
  `C(ω)↾pn = codeList p (ω↾n)` (`wordPrefix_blockCode`) with `codeList p` computable.

Blueprint node `erg:symbolic-lower`.
-/

namespace Kolmogorov.PointToSet.SymbolicLower

open Filter Set MeasureTheory
open scoped ENNReal

/-! ### Closure of computable real families under computable finite sums -/

section listSum

/-- Mapping a relatively computable function over a relatively computable list. -/
lemma computableIn_list_map {O : Set (ℕ →. ℕ)} {γ σ τ : Type*} [Primcodable γ] [Primcodable σ]
    [Primcodable τ] [Inhabited σ] {f : γ → List σ} {g : γ → σ → τ}
    (hf : ComputableIn O f) (hg : ComputableIn O fun x : γ × σ ↦ g x.1 x.2) :
    ComputableIn O fun x ↦ (f x).map (g x) := by
  have hrec : ∀ x, ∀ n ≤ (f x).length,
      (Nat.rec [] (fun i acc ↦ acc ++ [g x ((f x).getD i default)]) n : List τ) =
        ((f x).take n).map (g x) := by
    intro x n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n < (f x).length := hn
      rw [List.take_add_one, List.map_append, ← ih hn'.le, List.getElem?_eq_getElem hn']
      simp [List.getElem?_eq_getElem hn']
  have hlen : ComputableIn O fun x ↦ (f x).length :=
    (Computable.computableIn Primrec.list_length.to_comp).comp hf
  have h1 : ComputableIn O fun q : γ × (ℕ × List τ) ↦ (f q.1).getD q.2.1 default :=
    (Computable.computableIn (Primrec.list_getD default).to_comp).comp
      ((hf.comp ComputableIn.fst).pair (ComputableIn.fst.comp ComputableIn.snd))
  have h2 : ComputableIn O fun q : γ × (ℕ × List τ) ↦ g q.1 ((f q.1).getD q.2.1 default) :=
    hg.comp (ComputableIn.fst.pair h1)
  have hstep : ComputableIn₂ O fun (x : γ) (q : ℕ × List τ) ↦
      q.2 ++ [g x ((f x).getD q.1 default)] :=
    (Computable.computableIn Primrec.list_concat.to_comp).comp
      ((ComputableIn.snd.comp ComputableIn.snd).pair h2)
  refine (ComputableIn.nat_rec hlen (ComputableIn.const []) hstep).of_eq fun x ↦ ?_
  have := hrec x _ le_rfl
  rw [List.take_length] at this
  exact this

/-- `l ↦ c ∑ l` is computable on lists of rationals. -/
private lemma computable_scaledSum (c : ℚ) : Computable fun l : List ℚ ↦ c * l.sum := by
  have hadd : Computable₂ fun (_ : List ℚ) (q : ℚ × ℚ) ↦ q.1 + q.2 :=
    Kolmogorov.computable₂_ratAdd.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  have hsum : Computable fun l : List ℚ ↦ l.foldr (fun b s ↦ b + s) (0 : ℚ) :=
    Computable.list_foldr (h := fun (_ : List ℚ) (q : ℚ × ℚ) ↦ q.1 + q.2) Computable.id
      (Computable.const (0 : ℚ)) hadd
  have hmul : Computable fun l : List ℚ ↦ c * l.foldr (fun b s ↦ b + s) (0 : ℚ) :=
    Kolmogorov.computable₂_ratMul.comp (Computable.const c) hsum
  refine hmul.of_eq fun l ↦ ?_
  rw [List.sum_eq_foldr]

/-- `|∑ a - ∑ b| ≤ n ε` when each `|a x - b x| ≤ ε` on a list of length `n`. -/
private lemma abs_list_sum_sub_le {δ : Type*} (l : List δ) (a b : δ → ℝ) (ε : ℝ)
    (h : ∀ x ∈ l, |a x - b x| ≤ ε) :
    |(l.map a).sum - (l.map b).sum| ≤ l.length * ε := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih fun y hy ↦ h y (by simp [hy])
    push_cast
    calc |a x + (t.map a).sum - (b x + (t.map b).sum)|
        = |(a x - b x) + ((t.map a).sum - (t.map b).sum)| := by ring_nf
      _ ≤ |a x - b x| + |(t.map a).sum - (t.map b).sum| := abs_add_le _ _
      _ ≤ ε + t.length * ε := add_le_add h1 h2
      _ = (t.length + 1) * ε := by ring

/-- A constant `c` (`|c| ≤ 1`) times the sum of a computable real family over a computable list
of indices is a computable real family. -/
lemma isComputableRealFamilyIn_listSum {α δ : Type*} [Primcodable α] [Primcodable δ]
    [Inhabited δ] {A : Set ℕ} {f : δ → ℝ} (hf : IsComputableRealFamilyIn A f) {L : α → List δ}
    (hL : Computable L) (c : ℚ) (hc : |c| ≤ 1) :
    IsComputableRealFamilyIn A fun x ↦ (c : ℝ) * ((L x).map f).sum := by
  obtain ⟨q, hq, herr⟩ := hf
  refine ⟨fun xn ↦ c * ((L xn.1).map fun u ↦ q (u, xn.2 + (L xn.1).length)).sum, ?_, ?_⟩
  · have hmap : ComputableIn {charOracle A} fun xn : α × ℕ ↦
        (L xn.1).map fun u ↦ q (u, xn.2 + (L xn.1).length) := by
      refine computableIn_list_map (f := fun xn : α × ℕ ↦ L xn.1)
        (g := fun xn u ↦ q (u, xn.2 + (L xn.1).length)) ?_ ?_
      · exact (hL.comp Computable.fst).computableIn
      · refine hq.comp (ComputableIn.snd.pair ?_)
        exact Computable.computableIn (Primrec.nat_add.to_comp.comp
          (Computable.snd.comp Computable.fst)
          (Primrec.list_length.to_comp.comp (hL.comp (Computable.fst.comp Computable.fst))))
    exact (computable_scaledSum c).computableIn.comp hmap
  · intro x n
    set m := (L x).length with hm_def
    have hε : ∀ u ∈ L x, |(q (u, n + m) : ℝ) - f u| ≤ (2 : ℝ)⁻¹ ^ (n + m) :=
      fun u _ ↦ (herr u (n + m)).le
    have h1 := abs_list_sum_sub_le (L x) (fun u ↦ (q (u, n + m) : ℝ)) f _ hε
    have hcast : ((c * ((L x).map fun u ↦ q (u, n + m)).sum : ℚ) : ℝ) =
        (c : ℝ) * ((L x).map fun u ↦ (q (u, n + m) : ℝ)).sum := by
      rw [Rat.cast_mul, Rat.cast_list_sum, List.map_map]
      rfl
    simp only
    rw [hcast, ← mul_sub, abs_mul]
    have hm : (m : ℝ) * (2 : ℝ)⁻¹ ^ (n + m) < (2 : ℝ)⁻¹ ^ n := by
      have hlt : (m : ℝ) * (2 : ℝ)⁻¹ ^ m < 1 := by
        rw [inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
        exact_mod_cast Nat.lt_two_pow_self
      calc (m : ℝ) * (2 : ℝ)⁻¹ ^ (n + m) = (2 : ℝ)⁻¹ ^ n * ((m : ℝ) * (2 : ℝ)⁻¹ ^ m) := by
            rw [pow_add]; ring
        _ < (2 : ℝ)⁻¹ ^ n * 1 := mul_lt_mul_of_pos_left hlt (by positivity)
        _ = _ := mul_one _
    have hc' : |(c : ℝ)| ≤ 1 := by exact_mod_cast hc
    calc |(c : ℝ)| * |((L x).map fun u ↦ (q (u, n + m) : ℝ)).sum - ((L x).map f).sum|
        ≤ 1 * (m * (2 : ℝ)⁻¹ ^ (n + m)) := mul_le_mul hc' h1 (abs_nonneg _) zero_le_one
      _ < _ := by linarith

end listSum

/-! ### The cylinder measures of `ν''` as finite sums -/

section words

variable {p : ℕ}

/-- `((l.flatMap g).map F).sum = ∑_{a ∈ l} ((g a).map F).sum`. -/
lemma sum_map_flatMap {δ ε M : Type*} [AddCommMonoid M] (l : List δ) (g : δ → List ε)
    (F : ε → M) : ((l.flatMap g).map F).sum = (l.map fun a ↦ ((g a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, ih]

/-- `((List.range n).map F).sum = ∑_{j < n} F j`. -/
private lemma sum_map_range {M : Type*} [AddCommMonoid M] (F : ℕ → M) (n : ℕ) :
    ((List.range n).map F).sum = ∑ j ∈ Finset.range n, F j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
                 simp

/-- All the words of length `N` over `Fin p`, as lists. -/
def allWords (p N : ℕ) : List (List (Fin p)) :=
  (fun W : List (List (Fin p)) ↦ W.flatMap fun u ↦ (List.finRange p).map fun a ↦ a :: u)^[N] [[]]

/-- `allWords` is primitive recursive. -/
lemma primrec_allWords (p : ℕ) : Primrec (allWords p) := by
  have hcons : Primrec₂ fun (x : List (List (Fin p)) × List (Fin p)) (a : Fin p) ↦ a :: x.2 :=
    (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have hinner : Primrec₂ fun (_ : List (List (Fin p))) (u : List (Fin p)) ↦
      (List.finRange p).map fun a ↦ a :: u :=
    (Primrec.list_map (Primrec.const (List.finRange p)) hcons).to₂
  have hstep : Primrec fun W : List (List (Fin p)) ↦
      W.flatMap fun u ↦ (List.finRange p).map fun a ↦ a :: u :=
    Primrec.list_flatMap Primrec.id hinner
  exact (Primrec.nat_iterate' hstep).comp (Primrec.const [[]]) Primrec.id

/-- Summing over `allWords p N` is summing over the words `Fin N → Fin p`. -/
lemma sum_map_allWords {M : Type*} [AddCommMonoid M] (N : ℕ) (F : List (Fin p) → M) :
    ((allWords p N).map F).sum = ∑ w : Fin N → Fin p, F (List.ofFn w) := by
  induction N generalizing F with
  | zero => simp [allWords]
  | succ N ih =>
    have hstep : allWords p (N + 1) =
        (allWords p N).flatMap fun u ↦ (List.finRange p).map fun a ↦ a :: u := by
      simp only [allWords]
      rw [Function.iterate_succ_apply']
    rw [hstep, sum_map_flatMap]
    have hin : ∀ u : List (Fin p), (((List.finRange p).map fun a ↦ a :: u).map F).sum =
        ∑ a : Fin p, F (a :: u) := by
      intro u
      rw [List.map_map, Fin.sum_univ_def]
      rfl
    simp only [hin]
    rw [ih (fun u ↦ ∑ a : Fin p, F (a :: u))]
    rw [← (Fin.consEquiv fun _ : Fin (N + 1) ↦ Fin p).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    simp [Fin.consEquiv, List.ofFn_succ]

/-- Bit `m` of the block code of a word given by the list `l` of its symbols. -/
def codeAt (p : ℕ) (l : List ℕ) (m : ℕ) : Bool :=
  decide (l.getD (m / p) 0 = m % p)

/-- `codeAt` is primitive recursive. -/
lemma primrec_codeAt (p : ℕ) : Primrec₂ (codeAt p) :=
  (Primrec.eq.comp ((Primrec.list_getD 0).comp Primrec.fst
      (Primrec.nat_div.comp Primrec.snd (Primrec.const p)))
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const p))).decide

/-- The test "the binary word `v` sits at position `j` of the block code of `u`". -/
def condW (p j : ℕ) (v : List Bool) (u : List (Fin p)) : Bool :=
  (List.range v.length).all fun i ↦ decide (codeAt p (u.map Fin.val) (i + j) = v.getD i false)

/-- `condW` is primitive recursive. -/
lemma primrec_condW (p : ℕ) :
    Primrec fun x : ℕ × List Bool × List (Fin p) ↦ condW p x.1 x.2.1 x.2.2 := by
  have hval : Primrec fun x : ℕ × List Bool × List (Fin p) ↦ x.2.2.map Fin.val :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) (Primrec.fin_val.comp Primrec.snd).to₂
  have hp : Primrec₂ fun (x : ℕ × List Bool × List (Fin p)) (i : ℕ) ↦
      decide (codeAt p (x.2.2.map Fin.val) (i + x.1) = x.2.1.getD i false) :=
    (Primrec.eq.comp ((primrec_codeAt p).comp (hval.comp Primrec.fst)
      (Primrec.nat_add.comp Primrec.snd (Primrec.fst.comp Primrec.fst)))
      ((Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)).decide.to₂
  exact Kolmogorov.list_all_primrec
    (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))) hp

/-- The words of length `|v| + 1` contributing to `ν''[v]`, with multiplicity (one copy for
each shift `j < p`). -/
def wordList (p : ℕ) (v : List Bool) : List (List (Fin p)) :=
  (List.range p).flatMap fun j ↦
    (allWords p (v.length + 1)).flatMap fun u ↦ bif condW p j v u then [u] else []

/-- `wordList` is primitive recursive. -/
lemma primrec_wordList (p : ℕ) : Primrec (wordList p) := by
  have hc : Primrec₂ fun (x : List Bool × ℕ) (u : List (Fin p)) ↦
      bif condW p x.2 x.1 u then [u] else [] :=
    (Primrec.cond ((primrec_condW p).comp ((Primrec.snd.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const [])) (Primrec.const [])).to₂
  have hj : Primrec₂ fun (v : List Bool) (j : ℕ) ↦
      (allWords p (v.length + 1)).flatMap fun u ↦ bif condW p j v u then [u] else [] :=
    (Primrec.list_flatMap ((primrec_allWords p).comp
      (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst))) hc).to₂
  exact Primrec.list_flatMap (Primrec.const (List.range p)) hj

/-- Cylinders of finite words are measurable. -/
lemma measurableSet_listCylinder {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (v : List α) : MeasurableSet (listCylinder v) :=
  PointToSet.measurableSet_listCylinder v

/-- On the cylinder `[w]`, the list code reads off the block code. -/
lemma codeAt_ofFn {N : ℕ} {w : Fin N → Fin p} {ω : ℕ → Fin p} (hω : ω ∈ wordCylinder w)
    {m : ℕ} (hm : m / p < N) :
    codeAt p ((List.ofFn w).map Fin.val) m = blockCode p ω m := by
  have h := hω ⟨m / p, hm⟩
  simp only at h
  simp only [codeAt, blockCode]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp [h]

/-- On the cylinder `[w]` of a word of length `|v| + 1`, membership in `C⁻¹ σ^{-j} [v]` is
decided by `condW`. -/
lemma mem_preimage_iff_condW (hp : 0 < p) {j : ℕ} (hj : j < p) (v : List Bool)
    {w : Fin (v.length + 1) → Fin p} {ω : ℕ → Fin p} (hω : ω ∈ wordCylinder w) :
    ω ∈ blockCode p ⁻¹' (shiftMap^[j] ⁻¹' listCylinder v) ↔
      condW p j v (List.ofFn w) = true := by
  have hdiv : ∀ i < v.length, (i + j) / p < v.length + 1 := by
    intro i hi
    have : v.length ≤ v.length * p := Nat.le_mul_of_pos_right _ hp
    rw [Nat.div_lt_iff_lt_mul hp, Nat.succ_mul]
    omega
  simp only [mem_preimage, listCylinder, mem_ofPred_eq, iterate_shift, condW, List.all_eq_true,
    List.mem_range, decide_eq_true_eq]
  refine forall_congr' fun i ↦ ⟨fun h hi ↦ ?_, fun h hi ↦ ?_⟩
  · rw [codeAt_ofFn hω (hdiv i hi), h hi, List.getD_eq_getElem _ _ hi]
  · rw [← codeAt_ofFn hω (hdiv i hi), h hi, List.getD_eq_getElem _ _ hi]

/-- `ν(C⁻¹ σ^{-j} [v])` as a finite sum of cylinder measures. -/
lemma measure_preimage_eq_sum (ν : Measure (ℕ → Fin p)) (hp : 0 < p) {j : ℕ} (hj : j < p)
    (v : List Bool) :
    ν (blockCode p ⁻¹' (shiftMap^[j] ⁻¹' listCylinder v)) =
      ∑ w : Fin (v.length + 1) → Fin p,
        bif condW p j v (List.ofFn w) then ν (wordCylinder w) else 0 := by
  set S := blockCode p ⁻¹' (shiftMap^[j] ⁻¹' listCylinder v) with hS_def
  have hSm : MeasurableSet S :=
    measurable_blockCode ((measurable_shift.iterate j) (measurableSet_listCylinder v))
  have hS : S = ⋃ w ∈ (Finset.univ : Finset (Fin (v.length + 1) → Fin p)),
      S ∩ wordCylinder w := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, Finset.mem_univ, exists_true_left]
    exact ⟨fun h ↦ ⟨fun i ↦ ω i, h, fun i ↦ rfl⟩, fun ⟨_, h, _⟩ ↦ h⟩
  rw [hS, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun w _ ↦ ?_
    cases hc : condW p j v (List.ofFn w)
    · have : S ∩ wordCylinder w = ∅ := Set.eq_empty_of_forall_notMem fun ω hω ↦ by
        have h1 := (mem_preimage_iff_condW hp hj v hω.2).1 hω.1
        rw [hc] at h1
        exact Bool.false_ne_true h1
      rw [this, measure_empty]
      rfl
    · have : S ∩ wordCylinder w = wordCylinder w :=
        Set.inter_eq_right.2 fun ω h2 ↦ (mem_preimage_iff_condW hp hj v h2).2 hc
      rw [this]
      rfl
  · intro w _ w' _ hww'
    exact ((isMeasurablePartition_wordCylinder _).disjoint hww').mono inter_subset_right
      inter_subset_right
  · exact fun w _ ↦ hSm.inter (measurableSet_wordCylinder' w)

/-- `ν''[v] = (1/p) ∑_{u ∈ wordList p v} ν[u]`. -/
lemma blockAvg_listCylinder_toReal (ν : Measure (ℕ → Fin p)) [IsFiniteMeasure ν] (hp : 0 < p)
    (v : List Bool) :
    (blockAvg ν (listCylinder v)).toReal =
      ((1 / p : ℚ) : ℝ) * ((wordList p v).map fun u ↦ (ν (listCylinder u)).toReal).sum := by
  rw [blockAvg_apply ν (measurableSet_listCylinder v), wordList, sum_map_flatMap,
    sum_map_range, ENNReal.toReal_mul, ENNReal.toReal_sum fun j _ ↦ measure_ne_top _ _,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  rw [one_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hfin : ∀ w : Fin (v.length + 1) → Fin p,
      (bif condW p j v (List.ofFn w) then ν (wordCylinder w) else 0) ≠ ⊤ := by
    intro w
    cases condW p j v (List.ofFn w) <;> simp [measure_ne_top]
  rw [measure_preimage_eq_sum ν hp (Finset.mem_range.1 hj) v, sum_map_flatMap,
    sum_map_allWords, ENNReal.toReal_sum fun w _ ↦ hfin w]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  cases condW p j v (List.ofFn w) <;>
    simp only [Bool.cond_true, Bool.cond_false, listCylinder_ofFn, ENNReal.toReal_zero,
      List.map_nil, List.map_cons, List.sum_nil, List.sum_cons, add_zero]

/-- `ν''` is `A`-computable on cylinders when `ν` is. -/
lemma isComputableWordMeasureIn_blockAvg {A : Set ℕ} (ν : Measure (ℕ → Fin p))
    [IsFiniteMeasure ν] (hp : 0 < p) (hc : IsComputableWordMeasureIn A ν) :
    IsComputableWordMeasureIn A (blockAvg ν) := by
  have hc1 : |(1 / p : ℚ)| ≤ 1 := by
    have hp1 : (1 : ℚ) ≤ p := by exact_mod_cast hp
    rw [abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ hp1 (by positivity)
  have h := isComputableRealFamilyIn_listSum hc (primrec_wordList p).to_comp (1 / p : ℚ) hc1
  unfold IsComputableWordMeasureIn
  convert h using 1
  funext v
  exact blockAvg_listCylinder_toReal ν hp v

end words

/-! ### Randomness and complexity of the coded sequence -/

section transfer

variable {p : ℕ}

/-- On the cylinder `[u]` of a finite word, the list code reads off the block code. -/
lemma codeAt_of_mem_listCylinder {u : List (Fin p)} {ω : ℕ → Fin p} (hω : ω ∈ listCylinder u)
    {m : ℕ} (hm : m / p < u.length) :
    codeAt p (u.map Fin.val) m = blockCode p ω m := by
  simp only [codeAt, blockCode]
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getElem_map, hω (m / p) hm]

/-- The pull-back of the cylinder-union `⋃_{E(m + p, v)} [v]` under the block code is the union
of the cylinders of the words `u` such that some `v` with `E(m + p, v)` sits at the start of the
code of `u`. -/
lemma preimage_blockCode_iUnion (E : ℕ × List Bool → Prop) (m : ℕ) :
    blockCode p ⁻¹' (⋃ v ∈ {v | E (m + p, v)}, listCylinder v) =
      ⋃ u ∈ {u : List (Fin p) | ∃ v, E (m + p, v) ∧
        (v.length ≤ p * u.length ∧ condW p 0 v u = true)}, listCylinder u := by
  ext ω
  simp only [mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨v, hE, hv⟩
    have hp : 0 < p := Nat.pos_of_ne_zero fun h ↦ by subst h; exact (ω 0).elim0
    refine ⟨wordPrefix ω v.length, ⟨v, hE, ?_, ?_⟩, mem_listCylinder_wordPrefix ω _⟩
    · simp only [wordPrefix, List.length_ofFn]
      exact Nat.le_mul_of_pos_left _ hp
    · simp only [condW, List.all_eq_true, List.mem_range, decide_eq_true_eq, add_zero]
      intro i hi
      have hlt : i / p < (wordPrefix ω v.length).length := by
        simp only [wordPrefix, List.length_ofFn]
        exact lt_of_le_of_lt (Nat.div_le_self i p) hi
      rw [codeAt_of_mem_listCylinder (mem_listCylinder_wordPrefix ω _) hlt, hv i hi,
        List.getD_eq_getElem _ _ hi]
  · rintro ⟨u, ⟨v, hE, hlen, hcond⟩, hu⟩
    refine ⟨v, hE, fun i hi ↦ ?_⟩
    simp only [condW, List.all_eq_true, List.mem_range, decide_eq_true_eq, add_zero] at hcond
    have hlt : i / p < u.length := by
      have hp : 0 < p := Nat.pos_of_ne_zero fun h ↦ by subst h; exact (ω 0).elim0
      rw [Nat.div_lt_iff_lt_mul hp]
      rw [mul_comm] at hlen
      omega
    rw [← codeAt_of_mem_listCylinder hu hlt, hcond i hi, List.getD_eq_getElem _ _ hi]

/-- The test pulled back by the block code is r.e. -/
private lemma isREIn_pullback {A : Set ℕ} {E : ℕ × List Bool → Prop} (hE : IsREIn A E) :
    IsREIn A fun x : ℕ × List (Fin p) ↦ ∃ v : List Bool,
      (E (x.1 + p, v) ∧ (v.length ≤ p * x.2.length ∧ condW p 0 v x.2 = true)) := by
  refine IsREIn.exists (F := fun y : (ℕ × List (Fin p)) × List Bool ↦
    E (y.1.1 + p, y.2) ∧ (y.2.length ≤ p * y.1.2.length ∧ condW p 0 y.2 y.1.2 = true)) ?_
  refine IsREIn.and (hE.comp ?_) (isREIn_of_computable_decide ?_)
  · exact (Computable.pair (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.const p)) Computable.snd).computableIn
  · have hle : Primrec fun y : (ℕ × List (Fin p)) × List Bool ↦
        decide (y.2.length ≤ p * y.1.2.length) :=
      (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.nat_mul.comp (Primrec.const p)
          (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))).decide
    have hc : Primrec fun y : (ℕ × List (Fin p)) × List Bool ↦ condW p 0 y.2 y.1.2 :=
      (primrec_condW p).comp ((Primrec.const 0).pair (Primrec.snd.pair
        (Primrec.snd.comp Primrec.fst)))
    refine (Primrec.and.comp hle hc).to_comp.of_eq fun y ↦ ?_
    simp

/-- If `ω` is `ν`-random relative to `A`, then `C(ω)` is `ν''`-random relative to `A`. -/
lemma blockCode_mem_wordRandomPoints {A : Set ℕ} (ν : Measure (ℕ → Fin p)) (hp : 0 < p)
    {ω : ℕ → Fin p} (hω : ω ∈ wordRandomPoints A ν) :
    blockCode p ω ∈ wordRandomPoints A (blockAvg ν) := by
  rintro V ⟨E, hE, hV, hVm⟩
  set V' : ℕ → Set (ℕ → Fin p) := fun m ↦ ⋃ u ∈ {u : List (Fin p) | ∃ v, E (m + p, v) ∧
    (v.length ≤ p * u.length ∧ condW p 0 v u = true)}, listCylinder u with hV'_def
  have hpre : ∀ m, V' m = blockCode p ⁻¹' V (m + p) := by
    intro m
    rw [hV (m + p), preimage_blockCode_iUnion]
  have hmeas : ∀ m, MeasurableSet (V m) := by
    intro m
    rw [hV m]
    exact MeasurableSet.biUnion (Set.to_countable _) fun v _ ↦ measurableSet_listCylinder v
  have htest : IsWordTestIn A ν V' := by
    refine ⟨_, isREIn_pullback hE, fun m ↦ rfl, fun m ↦ ?_⟩
    rw [hpre m]
    calc ν (blockCode p ⁻¹' V (m + p)) ≤ p * blockAvg ν (V (m + p)) :=
          blockPush_le_blockAvg ν hp (hmeas _)
      _ ≤ p * (2 : ℝ≥0∞)⁻¹ ^ (m + p) := by gcongr; exact hVm _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
          rw [pow_add, mul_comm, mul_assoc]
          have h2 : (p : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ p ≤ 1 := by
            rw [← ENNReal.inv_pow, ← div_eq_mul_inv]
            refine ENNReal.div_le_of_le_mul ?_
            rw [one_mul]
            exact_mod_cast (Nat.lt_two_pow_self).le
          calc (2 : ℝ≥0∞)⁻¹ ^ m * ((2 : ℝ≥0∞)⁻¹ ^ p * p)
              = (2 : ℝ≥0∞)⁻¹ ^ m * ((p : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ p) := by rw [mul_comm (_ ^ p)]
            _ ≤ (2 : ℝ≥0∞)⁻¹ ^ m * 1 := by gcongr
            _ = _ := mul_one _
  obtain ⟨m, hm⟩ := hω V' htest
  refine ⟨m + p, fun h ↦ hm ?_⟩
  rw [hpre m]
  exact h

/-- The block code on finite words. -/
def codeList (p : ℕ) (u : List (Fin p)) : List Bool :=
  (List.range (p * u.length)).map (codeAt p (u.map Fin.val))

/-- `codeList` is primitive recursive. -/
lemma primrec_codeList (p : ℕ) : Primrec (codeList p) := by
  have hval : Primrec fun u : List (Fin p) ↦ u.map Fin.val :=
    Primrec.list_map Primrec.id (Primrec.fin_val.comp Primrec.snd).to₂
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const p)
    Primrec.list_length)) ((primrec_codeAt p).comp (hval.comp Primrec.fst) Primrec.snd).to₂

/-- `C(ω)↾(p n)` is the code of `ω↾n`. -/
lemma wordPrefix_blockCode (ω : ℕ → Fin p) (n : ℕ) :
    wordPrefix (blockCode p ω) (p * n) = codeList p (wordPrefix ω n) := by
  refine List.ext_getElem (by simp [wordPrefix, codeList]) fun i h1 h2 ↦ ?_
  have hi : i < p * n := by simpa [wordPrefix] using h1
  have hp : 0 < p := Nat.pos_of_ne_zero fun h ↦ by subst h; simp at hi
  have hdiv : i / p < (wordPrefix ω n).length := by
    simp only [wordPrefix, List.length_ofFn]
    rw [Nat.div_lt_iff_lt_mul hp, mul_comm]
    exact hi
  simp only [codeList, List.getElem_map, List.getElem_range]
  rw [codeAt_of_mem_listCylinder (mem_listCylinder_wordPrefix ω n) hdiv]
  simp [wordPrefix]

/-- `K^A(C(ω)↾(p n)) ≤ K^A(ω↾n) + O(1)`. -/
lemma exists_wordComplexity_blockCode_le (A : Set ℕ) (p : ℕ) :
    ∃ c : ℕ, ∀ (ω : ℕ → Fin p) (n : ℕ),
      wordComplexity A (blockCode p ω) (p * n) ≤ wordComplexity A ω n + c := by
  let G : ℕ → ℕ := fun i ↦
    Encodable.encode (codeList p ((Encodable.decode (α := List (Fin p)) i).getD []))
  have hG : Computable G :=
    Computable.encode.comp ((primrec_codeList p).to_comp.comp
      (Computable.option_getD Computable.decode (Computable.const [])))
  let F : List BitString →. BitString :=
    fun ws ↦ Part.some (natBits (G (decodeBits (ws.headD []))))
  have hF : PartrecIn {charOracle A} F := by
    have hd : Computable fun ws : List BitString ↦ ws.headD [] :=
      (Computable.option_getD Primrec.list_head?.to_comp (Computable.const [])).of_eq
        fun ws ↦ by cases ws <;> rfl
    exact ((natBits_computable.comp (hG.comp decodeBits_computable)).comp hd).partrecIn
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A 1 F hF
  refine ⟨c, fun ω n ↦ ?_⟩
  set i := Encodable.encode (wordPrefix ω n)
  have hGi : G i = Encodable.encode (wordPrefix (blockCode p ω) (p * n)) := by
    simp only [G, i, Encodable.encodek, Option.getD_some, wordPrefix_blockCode]
  have hmem : natBits (G i) ∈ F [natBits i] := by
    simp only [F, List.headD_cons, natBits, decodeBits_natBits]
    exact Part.mem_some _
  have h := hc [natBits i] (natBits (G i)) rfl hmem
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  simpa [wordComplexity, oracleNatComplexity, hGi] using h

end transfer

end Kolmogorov.PointToSet.SymbolicLower
