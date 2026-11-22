/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ExampleFiveFiveLowerAux
import KolmogorovMathlib.PointToSet.Measure.RandomNonAtom

/-!
# Example 5.5(1): a countably supported measure with a random point of entropy `1`

This file proves `exists_countable_atomic_random_upperLocalEntropy_eq_one'`, the core of
Example 5.5(1) (restated as `exists_countable_atomic_random_upperLocalEntropy_eq_one` in
`ExampleFiveFive.lean`): on Cantor space with the shift and its standard computable presentation
`cantorPresentation` there is a probability measure `μ` computable from the empty oracle,
carried by a countable set, with a `μ`-random point `z` such that `h̄_μ(σ, z) = 1`.

## Construction

* `ex55u_exists_approx` (`ex55l_exists_omega` of `ExampleFiveFiveLowerAux.lean`): the binary
  expansion `w` of Chaitin's `Ω` is Martin-Löf random, and the computable increasing rational
  approximations of `Ω` give a computable array of bits `b t k` with `b t k = w k` for all
  large `t` (by irrationality and the absence of long zero runs,
  `exists_computable_cantorPrefix_of_ratApprox`).
* Instead of the paper's enumeration of `⋃ₙ {Ω_t↾n : t > n}`, the sets are indexed by stages:
  `E_i = [b i ↾ c_i]`, where `c_i ≤ i` is the first position at which stages `i` and `i + 1`
  differ. Then `w ∈ E_i` for infinitely many `i` and every `y ≠ w` lies in finitely many `E_i`.
* Blocks `J_i = [N_i, N_{i+1})` with `N_i = 2^{i²}` (so `c_i ≤ N_i` and `N_i / N_{i+1} → 0`).
  The map `f` puts `1 y_{N_i+1} … y_{N_{i+1}-1}` on `J_i` if `y ∈ E_i` and `0^{|J_i|}` otherwise.
  Divergence from the paper: the first bit of a block is the marker `1` instead of `y_{N_i}`, so
  that `f(w)` is visibly nonzero on every block `J_i` with `w ∈ E_i`; this gives
  `μ[f(w)↾N_{i+1}] ≤ 2^{-(N_{i+1}-N_i-1)}` without a randomness argument for the blocks.
* `f` is given on prefixes by the computable word map `ex55u_F`, so the infrastructure of
  `CantorPresentation.lean` gives admissibility of `μ = λ ∘ f⁻¹` and randomness of `f(w)`;
  `f(y)` is eventually `0` for `y ≠ w`, hence `μ` is carried by the eventually-`0` sequences;
  `h̄_μ(σ, f(w)) ≤ 1` by causality and `≥ 1` by `one_le_upperLocalEntropy_of_frequently`.

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- The block boundaries `N_i = 2^{i²}`; the `i`-th block is `J_i = [N_i, N_{i+1})`. -/
def ex55u_N (i : ℕ) : ℕ := 2 ^ (i * i)

/-- Whether the approximations `b (i+1)` and `b i` agree at all positions `≤ k`. -/
def ex55u_stable (b : ℕ → ℕ → Bool) (i k : ℕ) : Bool :=
  !((List.range (k + 1)).any fun k' ↦ !decide (b (i + 1) k' = b i k'))

/-- Whether the word `w` lies in `E_i`, the cylinder of `b i` restricted to the positions before
the first change between stages `i` and `i + 1` (and before `i`). -/
def ex55u_inE (b : ℕ → ℕ → Bool) (i : ℕ) (w : List Bool) : Bool :=
  !((List.range i).any fun k ↦ ex55u_stable b i k && !decide (w.getD k false = b i k))

/-- The `j`-th output bit of the word map: if `j` lies in the block `J_i`, it is `1` at
`j = N_i` and `w_j` elsewhere when `w ∈ E_i`, and `0` when `w ∉ E_i`. -/
def ex55u_G (b : ℕ → ℕ → Bool) (w : List Bool) (j : ℕ) : Bool :=
  (List.range (j + 1)).any fun i ↦ decide (ex55u_N i ≤ j) && decide (j < ex55u_N (i + 1)) &&
    ex55u_inE b i w && (decide (j = ex55u_N i) || w.getD j false)

/-- The length-preserving word map `F` of Example 5.5(1). -/
def ex55u_F (b : ℕ → ℕ → Bool) (w : List Bool) : List Bool :=
  (List.range w.length).map (ex55u_G b w)

/-- Equality of booleans is computable. -/
private lemma computable_decide_eq_bool : Computable₂ fun a b : Bool ↦ decide (a = b) :=
  primrec_decideEq.to_comp

/-- The word map `F` is computable when the approximations `b` are. -/
theorem ex55u_computable_F {b : ℕ → ℕ → Bool} (hb : Computable₂ b) :
    Computable (ex55u_F b) := by
  have hN : Computable ex55u_N :=
    Computable.pow2.comp (Primrec.nat_mul.to_comp.comp Computable.id Computable.id)
  have hle : Computable₂ fun a c : ℕ ↦ decide (a ≤ c) :=
    (PrimrecRel.decide Primrec.nat_le).to_comp
  have hlt : Computable₂ fun a c : ℕ ↦ decide (a < c) :=
    (PrimrecRel.decide Primrec.nat_lt).to_comp
  have hst : Computable₂ (ex55u_stable b) := by
    have : Computable fun z : ℕ × ℕ ↦ (List.range (z.2 + 1)).any fun k' ↦
        !decide (b (z.1 + 1) k' = b z.1 k') :=
      computable_list_any (Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.snd))
        (Primrec.not.to_comp.comp (computable_decide_eq_bool.comp
          (hb.comp (Computable.succ.comp (Computable.fst.comp Computable.fst)) Computable.snd)
          (hb.comp (Computable.fst.comp Computable.fst) Computable.snd))).to₂
    exact (Primrec.not.to_comp.comp this).to₂
  have hinE : Computable₂ (ex55u_inE b) := by
    have : Computable fun z : ℕ × List Bool ↦ (List.range z.1).any fun k ↦
        ex55u_stable b z.1 k && !decide (z.2.getD k false = b z.1 k) :=
      computable_list_any (Primrec.list_range.to_comp.comp Computable.fst)
        (Primrec.and.to_comp.comp (hst.comp (Computable.fst.comp Computable.fst) Computable.snd)
          (Primrec.not.to_comp.comp (computable_decide_eq_bool.comp
            ((Primrec.list_getD false).to_comp.comp (Computable.snd.comp Computable.fst)
              Computable.snd)
            (hb.comp (Computable.fst.comp Computable.fst) Computable.snd)))).to₂
    exact (Primrec.not.to_comp.comp this).to₂
  have hG : Computable₂ (ex55u_G b) := by
    refine Computable.to₂ (f := fun z : List Bool × ℕ ↦ ex55u_G b z.1 z.2)
      (computable_list_any (f := fun z : List Bool × ℕ ↦ List.range (z.2 + 1))
      (Primrec.list_range.to_comp.comp (Computable.succ.comp Computable.snd)) ?_)
    have hj : Computable fun z : (List Bool × ℕ) × ℕ ↦ z.1.2 :=
      Computable.snd.comp Computable.fst
    have hw : Computable fun z : (List Bool × ℕ) × ℕ ↦ z.1.1 :=
      Computable.fst.comp Computable.fst
    exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp
      (hle.comp (hN.comp Computable.snd) hj) (hlt.comp hj (hN.comp (Computable.succ.comp
        Computable.snd)))) (hinE.comp Computable.snd hw))
      (Primrec.or.to_comp.comp (primrec_decideEq.to_comp.comp hj (hN.comp Computable.snd))
        ((Primrec.list_getD false).to_comp.comp hw hj))).to₂
  exact Computable.list_map (Primrec.list_range.to_comp.comp Computable.list_length) hG

/-- The fair-coin measure of the set of sequences agreeing with `w` on a finite set `s` is
`2^{-|s|}`. -/
lemma ex55u_measure_pi (w : ℕ → Bool) (s : Finset ℕ) :
    uniformMeasure (Set.pi (s : Set ℕ) fun j ↦ {w j}) = (2 : ℝ≥0∞)⁻¹ ^ s.card := by
  set ν := ProbabilityTheory.bernoulliMeasure true false
    ⟨((1 / 2 : NNReal) : ℝ), by norm_num, by norm_num⟩ with hν
  have hU : uniformMeasure = Measure.infinitePi fun _ : ℕ ↦ ν := rfl
  rw [hU]
  refine (Measure.infinitePi_pi (μ := fun _ : ℕ ↦ ν) (s := s) (t := fun j ↦ {w j})
    (fun _ _ ↦ measurableSet_singleton _)).trans ?_
  rw [Finset.prod_congr rfl (g := fun _ ↦ (2 : ℝ≥0∞)⁻¹), Finset.prod_const]
  intro j _
  cases w j
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
      (measurableSet_singleton false) (by simp) rfl]
    have h : unitInterval.toNNReal (unitInterval.symm
        ⟨((1 / 2 : NNReal) : ℝ), by norm_num, by norm_num⟩) = 2⁻¹ := by
      ext; simp [unitInterval.coe_symm_eq]; norm_num
    rw [h, ENNReal.coe_inv two_ne_zero]
    rfl
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
      (measurableSet_singleton true) rfl (by simp)]
    have h : unitInterval.toNNReal ⟨((1 / 2 : NNReal) : ℝ), by norm_num, by norm_num⟩ =
        2⁻¹ := by
      ext; simp
    rw [h, ENNReal.coe_inv two_ne_zero]
    rfl

/-! ### The blocks and the sets `E_i` -/

section logic

variable {b : ℕ → ℕ → Bool}

/-- The block boundaries are strictly increasing. -/
lemma ex55u_N_strictMono : StrictMono ex55u_N := fun _ _ h ↦
  Nat.pow_lt_pow_right (by norm_num) (Nat.mul_self_lt_mul_self h)

/-- `i ≤ N_i`. -/
lemma ex55u_le_N (i : ℕ) : i ≤ ex55u_N i :=
  (Nat.le_mul_self i).trans (Nat.lt_two_pow_self).le

/-- A position lies in at most one block. -/
lemma ex55u_block_unique {i i' j : ℕ} (h1 : ex55u_N i ≤ j) (h2 : j < ex55u_N (i + 1))
    (h3 : ex55u_N i' ≤ j) (h4 : j < ex55u_N (i' + 1)) : i = i' := by
  by_contra h
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := ex55u_N_strictMono.monotone (show i + 1 ≤ i' by omega); omega
  · have := ex55u_N_strictMono.monotone (show i' + 1 ≤ i by omega); omega

/-- The length `c_i ≤ i` of the word defining `E_i`: the first position at which the
approximations of stages `i` and `i + 1` differ, or `i` if there is none below `i`. -/
def ex55u_c (b : ℕ → ℕ → Bool) (i : ℕ) : ℕ :=
  Nat.find (p := fun k ↦ k = i ∨ b (i + 1) k ≠ b i k) ⟨i, Or.inl rfl⟩

/-- `c_i ≤ i`. -/
lemma ex55u_c_le (i : ℕ) : ex55u_c b i ≤ i := Nat.find_min' _ (Or.inl rfl)

/-- `c_i` is `i` or a position where stages `i` and `i + 1` differ. -/
lemma ex55u_c_spec (i : ℕ) :
    ex55u_c b i = i ∨ b (i + 1) (ex55u_c b i) ≠ b i (ex55u_c b i) :=
  Nat.find_spec (p := fun k ↦ k = i ∨ b (i + 1) k ≠ b i k) ⟨i, Or.inl rfl⟩

/-- Below `c_i` the approximations of stages `i` and `i + 1` agree. -/
lemma ex55u_stable_of_lt_c {i k : ℕ} (hk : k < ex55u_c b i) : b (i + 1) k = b i k := by
  have := Nat.find_min (p := fun k ↦ k = i ∨ b (i + 1) k ≠ b i k) ⟨i, Or.inl rfl⟩ hk
  push Not at this
  exact this.2

/-- `ex55u_stable` in propositional form. -/
lemma ex55u_stable_iff (i k : ℕ) :
    ex55u_stable b i k = true ↔ ∀ k' ≤ k, b (i + 1) k' = b i k' := by
  simp [ex55u_stable]

/-- `w ∈ E_i` iff `w` agrees with `b i` below `c_i`. -/
lemma ex55u_inE_iff (i : ℕ) (w : List Bool) :
    ex55u_inE b i w = true ↔ ∀ k < ex55u_c b i, w.getD k false = b i k := by
  have h : ex55u_inE b i w = true ↔
      ∀ k < i, ex55u_stable b i k = true → w.getD k false = b i k := by
    simp [ex55u_inE]
  rw [h]
  constructor
  · intro h k hk
    exact h k (lt_of_lt_of_le hk (ex55u_c_le i)) ((ex55u_stable_iff i k).2 fun k' hk' ↦
      ex55u_stable_of_lt_c (lt_of_le_of_lt hk' hk))
  · intro h k hki hst
    refine h k ?_
    by_contra hc
    push Not at hc
    rcases ex55u_c_spec (b := b) i with h' | h'
    · omega
    · exact h' ((ex55u_stable_iff i k).1 hst _ hc)

/-- `ex55u_G` in propositional form. -/
lemma ex55u_G_iff (w : List Bool) (j : ℕ) :
    ex55u_G b w j = true ↔ ∃ i, ex55u_N i ≤ j ∧ j < ex55u_N (i + 1) ∧
      (∀ k < ex55u_c b i, w.getD k false = b i k) ∧
        (j = ex55u_N i ∨ w.getD j false = true) := by
  simp only [ex55u_G, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, ex55u_inE_iff]
  constructor
  · rintro ⟨i, -, ⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨i, h1, h2, h3, h4⟩
  · rintro ⟨i, h1, h2, h3, h4⟩
    exact ⟨i, by have := ex55u_le_N i; omega, ⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- The symbols of a prefix word. -/
lemma ex55u_getD_wordPrefix (y : ℕ → Bool) {n k : ℕ} (hk : k < n) :
    (wordPrefix y n).getD k false = y k := by
  simp [wordPrefix, List.getD_eq_getElem?_getD, hk]

/-- The `j`-th bit of `f(y)` is `1`: `j ∈ J_i` with `y ∈ E_i`, and `j = N_i` or `y_j = 1`. -/
def ex55u_spec (b : ℕ → ℕ → Bool) (y : ℕ → Bool) (j : ℕ) : Prop :=
  ∃ i, ex55u_N i ≤ j ∧ j < ex55u_N (i + 1) ∧ (∀ k < ex55u_c b i, y k = b i k) ∧
    (j = ex55u_N i ∨ y j = true)

/-- On a prefix of `y` longer than `j`, the `j`-th output bit is described by `ex55u_spec`. -/
lemma ex55u_G_wordPrefix_iff (y : ℕ → Bool) {n j : ℕ} (hj : j < n) :
    ex55u_G b (wordPrefix y n) j = true ↔ ex55u_spec b y j := by
  rw [ex55u_G_iff, ex55u_spec, ex55u_getD_wordPrefix y hj]
  refine exists_congr fun i ↦ and_congr_right fun h1 ↦ and_congr_right fun _ ↦
    and_congr_left fun _ ↦ forall₂_congr fun k hk ↦ ?_
  have := (ex55u_c_le (b := b) i).trans (ex55u_le_N i)
  rw [ex55u_getD_wordPrefix y (by omega)]

/-- The causal map `f` of Example 5.5(1): on the block `J_i`, `f(y)` is `1 y_{N_i+1} …` if
`y ∈ E_i` and `0^{|J_i|}` otherwise. -/
def ex55u_f (b : ℕ → ℕ → Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun j ↦ ex55u_G b (wordPrefix y (j + 1)) j

/-- The bits of `f(y)`. -/
lemma ex55u_f_iff (y : ℕ → Bool) (j : ℕ) : ex55u_f b y j = true ↔ ex55u_spec b y j :=
  ex55u_G_wordPrefix_iff y (Nat.lt_succ_self j)

/-- `f` is given on prefixes by the word map `F`: `f(y)↾n = F(y↾n)`. -/
theorem ex55u_wordPrefix_f (y : ℕ → Bool) (n : ℕ) :
    wordPrefix (ex55u_f b y) n = ex55u_F b (wordPrefix y n) := by
  refine List.ext_getElem (by simp [wordPrefix, ex55u_F]) fun j h1 h2 ↦ ?_
  have hj : j < n := by simpa [wordPrefix] using h1
  simp only [wordPrefix, List.getElem_ofFn, ex55u_F, List.getElem_map, List.getElem_range]
  exact Bool.eq_iff_iff.2 (by rw [ex55u_f_iff, ← wordPrefix, ex55u_G_wordPrefix_iff y hj])

/-- The bits of `f(y)` inside the block `J_i`. -/
lemma ex55u_f_block (y : ℕ → Bool) {i j : ℕ} (h1 : ex55u_N i ≤ j)
    (h2 : j < ex55u_N (i + 1)) : ex55u_f b y j = true ↔
      (∀ k < ex55u_c b i, y k = b i k) ∧ (j = ex55u_N i ∨ y j = true) := by
  rw [ex55u_f_iff]
  constructor
  · rintro ⟨i', h3, h4, h5, h6⟩
    obtain rfl := ex55u_block_unique h1 h2 h3 h4
    exact ⟨h5, h6⟩
  · rintro ⟨h5, h6⟩
    exact ⟨i, h1, h2, h5, h6⟩

section approx

variable {w : ℕ → Bool} (hb : ∀ k, ∀ᶠ t in atTop, b t k = w k)
include hb

/-- If the approximations converge to `w` bitwise, then `w ∈ E_i` for infinitely many `i`: take
`i ≥ K` minimising `c_i`; the positions below `c_i` never change after stage `i`. -/
lemma ex55u_exists_mem_E (K : ℕ) : ∃ i ≥ K, ∀ k < ex55u_c b i, w k = b i k := by
  classical
  have hex : ∃ v, ∃ i ≥ K, ex55u_c b i = v := ⟨_, K, le_rfl, rfl⟩
  obtain ⟨i, hiK, hi⟩ := Nat.find_spec hex
  refine ⟨i, hiK, fun k hk ↦ ?_⟩
  have hmin : ∀ j ≥ i, ex55u_c b i ≤ ex55u_c b j := fun j hj ↦
    hi ▸ Nat.find_min' hex ⟨j, hiK.trans hj, rfl⟩
  have hconst : ∀ j ≥ i, b j k = b i k := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [ex55u_stable_of_lt_c (lt_of_lt_of_le hk (hmin j hj)), ih]
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hb k)
  have := hT (max T i) (le_max_left _ _)
  rw [hconst _ (le_max_right _ _)] at this
  exact this.symm

/-- If the approximations converge to `w` bitwise, every `y ≠ w` lies in only finitely many
`E_i` (`c_i → ∞` and `b i → w`). -/
lemma ex55u_eventually_not_mem_E {y : ℕ → Bool} (hy : y ≠ w) :
    ∀ᶠ i in atTop, ¬ ∀ k < ex55u_c b i, y k = b i k := by
  obtain ⟨p, hp⟩ := Function.ne_iff.1 hy
  have hall : ∀ᶠ t in atTop, ∀ k ∈ Finset.range (p + 1), b t k = w k :=
    (Filter.eventually_all_finset _).2 fun k _ ↦ hb k
  obtain ⟨T, hT⟩ := eventually_atTop.1 hall
  filter_upwards [eventually_ge_atTop (max T (p + 1))] with i hi h
  have hcp : p < ex55u_c b i := by
    by_contra hc
    push Not at hc
    rcases ex55u_c_spec (b := b) i with h' | h'
    · omega
    · exact h' (by rw [hT (i + 1) (by omega) _ (Finset.mem_range.2 (by omega)),
        hT i (by omega) _ (Finset.mem_range.2 (by omega))])
  exact hp (by rw [h p hcp, hT i (by omega) p (Finset.mem_range.2 (by omega))])

/-- For `y ≠ w` the sequence `f(y)` is eventually `0`. -/
lemma ex55u_eventually_false {y : ℕ → Bool} (hy : y ≠ w) :
    ∀ᶠ j in atTop, ex55u_f b y j = false := by
  obtain ⟨I, hI⟩ := eventually_atTop.1 (ex55u_eventually_not_mem_E hb hy)
  filter_upwards [eventually_ge_atTop (ex55u_N I)] with j hj
  by_contra h
  rw [Bool.not_eq_false, ex55u_f_iff] at h
  obtain ⟨i, h1, h2, h3, -⟩ := h
  have hIi : I ≤ i := by
    by_contra hlt
    have := ex55u_N_strictMono.monotone (show i + 1 ≤ I by omega)
    omega
  exact hI i hIi h3

end approx

/-- If `w ∈ E_i`, then `μ[f(w)↾N_{i+1}] ≤ 2^{-(N_{i+1} - N_i - 1)}` for `μ = λ ∘ f⁻¹`: a
preimage point must lie in `E_i` (the bit at `N_i` is `1`) and agree with `w` on
`(N_i, N_{i+1})`. -/
lemma ex55u_map_cylinder_le {w : ℕ → Bool} {i : ℕ} (hE : ∀ k < ex55u_c b i, w k = b i k) :
    uniformMeasure.map (ex55u_f b) (PiNat.cylinder (ex55u_f b w) (ex55u_N (i + 1))) ≤
      (2 : ℝ≥0∞)⁻¹ ^ (ex55u_N (i + 1) - ex55u_N i - 1) := by
  have hF : ∀ y n, wordPrefix (ex55u_f b y) n = ex55u_F b (wordPrefix y n) :=
    ex55u_wordPrefix_f
  have hlt : ex55u_N i < ex55u_N (i + 1) := ex55u_N_strictMono (Nat.lt_succ_self i)
  rw [cantorPres_map_cylinder hF, ← Nat.card_Ioo, ← ex55u_measure_pi w]
  refine measure_mono fun y hy ↦ ?_
  simp only [mem_ofPred_eq, ← hF] at hy
  have hcyl := cantorPres_wordPrefix_eq_iff.1 hy
  have heq : ∀ j < ex55u_N (i + 1), ex55u_f b y j = ex55u_f b w j := fun j hj ↦
    (PiNat.mem_cylinder_iff.1 hcyl) j hj
  have hw0 : ex55u_f b w (ex55u_N i) = true :=
    (ex55u_f_block w le_rfl hlt).2 ⟨hE, Or.inl rfl⟩
  have hyE := ((ex55u_f_block y le_rfl hlt).1 (by rw [heq _ hlt, hw0])).1
  simp only [Finset.coe_Ioo, Set.mem_pi, Set.mem_Ioo, Set.mem_singleton_iff]
  rintro j ⟨hj1, hj2⟩
  have hy' := ex55u_f_block (b := b) y hj1.le hj2
  have hw' := ex55u_f_block (b := b) w hj1.le hj2
  have hne : j ≠ ex55u_N i := hj1.ne'
  refine Bool.eq_iff_iff.2 ?_
  rw [← heq j hj2] at hw'
  simp only [hne, false_or] at hy' hw'
  rw [← hw'.trans (and_iff_right hE), hy'.trans (and_iff_right hyE)]

end logic

/-- A Martin-Löf random sequence `w` (the binary expansion of an `Ω` number) with a computable
array of bit approximations `b t k → w k` (this is `ex55l_exists_omega`). -/
theorem ex55u_exists_approx : ∃ (w : ℕ → Bool) (b : ℕ → ℕ → Bool),
    IsMartinLofRandom uniformMeasure w ∧ Computable₂ b ∧
      ∀ k, ∀ᶠ t in atTop, b t k = w k :=
  ex55l_exists_omega

/-- `2^{-k}` in `ℝ≥0∞` as a real power. -/
lemma ex55u_inv_two_pow_eq (k : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ k = ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℝ))) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.inv_pow]

/-- `N_{i+1} = N_i · 2^{2i+1}`. -/
lemma ex55u_N_succ (i : ℕ) : ex55u_N (i + 1) = ex55u_N i * (2 * 2 ^ (2 * i)) := by
  rw [ex55u_N, ex55u_N, ← pow_succ', ← pow_add]
  congr 1
  ring

section entropy

attribute [local instance] cantorMetricSpace

/-- The lower bound `h̄_μ(σ, f(w)) ≥ 1` for `μ = λ ∘ f⁻¹`: for the infinitely many `i` with
`w ∈ E_i`, `μ[f(w)↾N_{i+1}] ≤ 2^{-(N_{i+1} - N_i - 1)}` and `N_i / N_{i+1} → 0`. -/
lemma ex55u_one_le {b : ℕ → ℕ → Bool} {w : ℕ → Bool}
    (hb : ∀ k, ∀ᶠ t in atTop, b t k = w k) :
    1 ≤ (localEntropy (uniformMeasure.map (ex55u_f b)) shiftMap (ex55u_f b w)).2 := by
  refine one_le_upperLocalEntropy_of_frequently _ _ fun δ hδ ↦ ?_
  rw [frequently_atTop]
  intro M
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
  obtain ⟨i, hi, hE⟩ := ex55u_exists_mem_E hb (max M K)
  have hlt : ex55u_N i < ex55u_N (i + 1) := ex55u_N_strictMono (Nat.lt_succ_self i)
  refine ⟨ex55u_N (i + 1), ?_, ?_⟩
  · have := ex55u_le_N (i + 1)
    omega
  refine (ex55u_map_cylinder_le hE).trans ?_
  rw [ex55u_inv_two_pow_eq]
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  -- the exponent estimate `(1 - δ) N_{i+1} ≤ N_{i+1} - N_i - 1`
  have hX : (i : ℝ) < 2 ^ (2 * i) := by
    have h1 : i < 2 ^ i := Nat.lt_two_pow_self
    have h2 : 2 ^ i ≤ 2 ^ (2 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h1.trans_le h2
  have hKi : (K : ℝ) ≤ i := by exact_mod_cast (le_max_right M K).trans hi
  have hδX : 1 ≤ δ * 2 ^ (2 * i) := by
    have : 1 / δ < 2 ^ (2 * i) := by linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hN1 : (1 : ℝ) ≤ ex55u_N i := by
    have : 1 ≤ ex55u_N i := Nat.one_le_two_pow
    exact_mod_cast this
  have hsucc : (ex55u_N (i + 1) : ℝ) = ex55u_N i * (2 * 2 ^ (2 * i)) := by
    rw [ex55u_N_succ]
    push_cast
    ring
  have hsub : ((ex55u_N (i + 1) - ex55u_N i - 1 : ℕ) : ℝ) =
      (ex55u_N (i + 1) : ℝ) - ex55u_N i - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hlt.le]
    push_cast
    ring
  rw [hsub, hsucc]
  have : (ex55u_N i : ℝ) * 2 ≤ ex55u_N i * (2 * (δ * 2 ^ (2 * i))) := by
    have := mul_le_mul_of_nonneg_left hδX (by positivity : (0 : ℝ) ≤ ex55u_N i * 2)
    nlinarith
  nlinarith

end entropy

attribute [local instance] cantorMetricSpace

/-- Example 5.5(1), core construction (proof of
`exists_countable_atomic_random_upperLocalEntropy_eq_one`): a measure on Cantor space computable
from the empty oracle for the standard presentation `cantorPresentation`, carried by a countable
set, with a random point of upper local entropy `1`. Blueprint node `meas:examples`. -/
theorem exists_countable_atomic_random_upperLocalEntropy_eq_one' :
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      IsMeasureAdmissible cantorPresentation shiftMap μ ∅ ∧
      (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
      ∃ z ∈ randomPoints cantorPresentation ∅ μ, (localEntropy μ shiftMap z).2 = 1 := by
  obtain ⟨w, b, hw, hbc, hb⟩ := ex55u_exists_approx
  have hFc := ex55u_computable_F hbc
  have hF : ∀ y n, wordPrefix (ex55u_f b y) n = ex55u_F b (wordPrefix y n) :=
    ex55u_wordPrefix_f
  have hmeas := cantorPres_measurable hF
  have hae : ∀ᵐ y ∂uniformMeasure, y ≠ w := by
    rw [ae_iff]
    simpa using uniformMeasure_singleton w
  refine ⟨uniformMeasure.map (ex55u_f b),
    inferInstance,
    cantorPres_isMeasureAdmissible_map_uniformMeasure ∅ hFc hF,
    exists_countable_map_compl_eq_zero _ hmeas.aemeasurable
      (hae.mono fun y hy ↦ ex55u_eventually_false hb hy),
    ex55u_f b w, cantorPres_map_mem_randomPoints_of_isMartinLofRandom hFc hF hw,
    le_antisymm (localEntropy_map_uniformMeasure_le_one hmeas.aemeasurable
      (cantorPres_causal hF) w).2 (ex55u_one_le hb)⟩

end Kolmogorov.PointToSet
