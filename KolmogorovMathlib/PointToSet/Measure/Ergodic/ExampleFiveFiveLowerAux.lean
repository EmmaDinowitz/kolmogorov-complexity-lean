/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.CantorPresentation
import KolmogorovMathlib.MonotoneComplexity.Omega.SolovayFunctions.BusyBeaverOmega

/-!
# Example 5.5(2): the word map and the random real

Combinatorial and computability input for `ExampleFiveFiveLower`.

* `ex55l_exists_omega`: a Martin-Löf random sequence `Ω` (the binary expansion of Chaitin's `Ω`)
  together with a computable family of approximations `W t` whose bits stabilise to those of `Ω`
  (`W t j = Ω j` for all large `t`). Built from the computable increasing rational approximations
  of `Ω` (`exists_computable_ratApprox_le_BPlain`) and the bit decoder of
  `exists_computable_cantorPrefix_of_ratApprox`.
* The block structure `N k = k^(k+1)` (`ex55l_N`), blocks `J_k = [N_k, N_{k+1})`, and the events
  `E_k = ex55l_In W k`: for `k = ⟨n, t⟩` (`Nat.unpair`), `y ∈ E_k` iff `n < t`, the prefix
  `W t↾n` is new at stage `t` (`t = n + 1` or `W t↾n ≠ W (t-1)↾n`), and `y↾n = W t↾n`. It is
  decided by `y↾n`, and `n ≤ k ≤ N_k`.
* The word map `ex55l_F W`, which replaces the block `J_k` of `y` by zeros when `y ∈ E_k`; it is
  computable, length preserving and monotone, so `CantorPres.seqMap (ex55l_F W)` is the causal map
  `f'` of Example 5.5(2) (`ex55l_seqMap_of_in`, `ex55l_seqMap_of_not_in`).

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### Block boundaries -/

/-- The block boundaries `N_k = k^(k+1)` of Example 5.5(2); the `k`-th block is
`[N_k, N_{k+1})`. -/
def ex55l_N (k : ℕ) : ℕ := k ^ (k + 1)

/-- `k ≤ N_k`. -/
lemma ex55l_le_N (k : ℕ) : k ≤ ex55l_N k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ex55l_N]
  · calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ (k + 1) := Nat.pow_le_pow_right hk (by omega)

/-- `k² ≤ N_k` for `k ≥ 1`. -/
lemma ex55l_sq_le_N {k : ℕ} (hk : 1 ≤ k) : k * k ≤ ex55l_N k := by
  calc k * k = k ^ 2 := (sq k).symm
    _ ≤ k ^ (k + 1) := Nat.pow_le_pow_right hk (by omega)

/-- The window `[N_k, N_k + k + 1)` lies inside the block `[N_k, N_{k+1})`. -/
lemma ex55l_N_window (k : ℕ) : ex55l_N k + k + 1 ≤ ex55l_N (k + 1) := by
  unfold ex55l_N
  have h1 : k ^ (k + 1) + 1 ≤ (k + 1) ^ (k + 1) :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self k) (by omega)
  have h2 : (k + 1) ^ (k + 1 + 1) = (k + 1) ^ (k + 1) * (k + 1) := pow_succ _ _
  have h3 : 1 ≤ (k + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  rw [h2]
  nlinarith

/-- `m · N_k ≤ N_{k+1}` for `m ≤ k + 1`. -/
lemma ex55l_mul_N_le {k m : ℕ} (hm : m ≤ k + 1) : m * ex55l_N k ≤ ex55l_N (k + 1) := by
  unfold ex55l_N
  have h1 : k ^ (k + 1) ≤ (k + 1) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_succ k) _
  calc m * k ^ (k + 1) ≤ (k + 1) * (k + 1) ^ (k + 1) := Nat.mul_le_mul hm h1
    _ = (k + 1) ^ (k + 1 + 1) := by ring

/-- The block boundaries are strictly increasing. -/
lemma ex55l_N_strictMono : StrictMono ex55l_N :=
  strictMono_nat_of_lt_succ fun k ↦ by have := ex55l_N_window k; omega

/-- If `N_a ≤ j < N_{b+1}` then `a ≤ b`. -/
lemma ex55l_le_of_N {a b j : ℕ} (h1 : ex55l_N a ≤ j) (h2 : j < ex55l_N (b + 1)) : a ≤ b := by
  by_contra h
  have := ex55l_N_strictMono.monotone (show b + 1 ≤ a by omega)
  omega

/-- Every position lies in a block. -/
lemma ex55l_exists_block (j : ℕ) : ∃ k, ex55l_N k ≤ j ∧ j < ex55l_N (k + 1) := by
  classical
  have hex : ∃ k, j < ex55l_N (k + 1) := ⟨j, by have := ex55l_le_N (j + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; simp [ex55l_N]
  · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel hpos] at hmin
    omega

/-- Blocks are disjoint. -/
lemma ex55l_block_unique {k k' j : ℕ} (h1 : ex55l_N k ≤ j) (h2 : j < ex55l_N (k + 1))
    (h1' : ex55l_N k' ≤ j) (h2' : j < ex55l_N (k' + 1)) : k = k' :=
  le_antisymm (ex55l_le_of_N h1 h2') (ex55l_le_of_N h1' h2)

/-! ### The events `E_k` and the word map -/

variable (W : ℕ → ℕ → Bool)

/-- The trigger of the index `k = ⟨n, t⟩`: `n < t`, and `W t↾n` is new at stage `t`
(`t = n + 1`, or `W t↾n ≠ W (t-1)↾n`). -/
def ex55l_trig (k : ℕ) : Bool :=
  decide (k.unpair.1 < k.unpair.2) &&
    (decide (k.unpair.2 = k.unpair.1 + 1) ||
      (List.range k.unpair.1).any fun j ↦ !decide (W k.unpair.2 j = W (k.unpair.2 - 1) j))

/-- The test `u ∈ E_k` on a word `u` (of length at least `n`, `k = ⟨n, t⟩`):
the trigger holds and `u↾n = W t↾n`. -/
def ex55l_inB (k : ℕ) (u : List Bool) : Bool :=
  ex55l_trig W k &&
    !(List.range k.unpair.1).any fun j ↦ !decide (W k.unpair.2 j = u.getD j false)

/-- Position `j` of a word `w` is zeroed: `j` lies in the block `J_k` and `w↾N_k ∈ E_k`. -/
def ex55l_zeroB (w : List Bool) (j : ℕ) : Bool :=
  (List.range (j + 1)).any fun k ↦
    (decide (ex55l_N k ≤ j) && decide (j < ex55l_N (k + 1))) &&
      ex55l_inB W k (w.take (ex55l_N k))

/-- The word map of Example 5.5(2): the blocks `J_k` with `w ∈ E_k` are replaced by zeros. -/
def ex55l_F (w : List Bool) : List Bool :=
  (List.range w.length).map fun j ↦ w.getD j false && !ex55l_zeroB W w j

/-- The event `E_k` on sequences: for `k = ⟨n, t⟩`, the trigger holds and `y↾n = W t↾n`. -/
def ex55l_In (k : ℕ) (y : ℕ → Bool) : Prop :=
  ex55l_trig W k = true ∧ ∀ j < k.unpair.1, W k.unpair.2 j = y j

/-- The trigger, unfolded. -/
lemma ex55l_trig_eq_true (k : ℕ) :
    ex55l_trig W k = true ↔ k.unpair.1 < k.unpair.2 ∧
      (k.unpair.2 = k.unpair.1 + 1 ∨
        ∃ j < k.unpair.1, W k.unpair.2 j ≠ W (k.unpair.2 - 1) j) := by
  simp [ex55l_trig, List.any_eq_true, List.mem_range]

/-- Entries of a prefix. -/
lemma ex55l_getD_wordPrefix (y : ℕ → Bool) {j m : ℕ} (h : j < m) :
    (wordPrefix y m).getD j false = y j := by
  simp [wordPrefix, List.getD_eq_getElem?_getD, h]

/-- The word test on a prefix of length at least `n` is the event `E_k`. -/
lemma ex55l_inB_wordPrefix (k : ℕ) (y : ℕ → Bool) {m : ℕ} (hm : k.unpair.1 ≤ m) :
    ex55l_inB W k (wordPrefix y m) = true ↔ ex55l_In W k y := by
  unfold ex55l_inB ex55l_In
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_range,
    Bool.not_eq_false, decide_eq_true_eq]
  refine and_congr Iff.rfl (forall₂_congr fun j hj ↦ ?_)
  rw [ex55l_getD_wordPrefix y (by omega)]

/-- `E_k` depends only on the first `N_k` coordinates. -/
lemma ex55l_In_congr (k : ℕ) {y v : ℕ → Bool} (h : ∀ j < ex55l_N k, v j = y j) :
    ex55l_In W k v ↔ ex55l_In W k y := by
  have hn : k.unpair.1 ≤ ex55l_N k := (Nat.unpair_left_le k).trans (ex55l_le_N k)
  unfold ex55l_In
  refine and_congr Iff.rfl (forall₂_congr fun j hj ↦ ?_)
  rw [h j (by omega)]

/-- The zero test on a prefix. -/
lemma ex55l_zeroB_wordPrefix (y : ℕ → Bool) {j m : ℕ} (hjm : j < m) :
    ex55l_zeroB W (wordPrefix y m) j = true ↔
      ∃ k, ex55l_N k ≤ j ∧ j < ex55l_N (k + 1) ∧ ex55l_In W k y := by
  unfold ex55l_zeroB
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, -, ⟨h1, h2⟩, h3⟩
    rw [PoincareAux.wordPrefix_take y (by omega)] at h3
    exact ⟨k, h1, h2, (ex55l_inB_wordPrefix W k y
      ((Nat.unpair_left_le k).trans (ex55l_le_N k))).1 h3⟩
  · rintro ⟨k, h1, h2, h3⟩
    refine ⟨k, by have := ex55l_le_N k; omega, ⟨h1, h2⟩, ?_⟩
    rw [PoincareAux.wordPrefix_take y (by omega)]
    exact (ex55l_inB_wordPrefix W k y ((Nat.unpair_left_le k).trans (ex55l_le_N k))).2 h3

/-- The word map preserves lengths. -/
lemma ex55l_length_F (w : List Bool) : (ex55l_F W w).length = w.length := by
  simp [ex55l_F]

/-- The zero test only reads the word below the position. -/
lemma ex55l_zeroB_take (w : List Bool) {j m : ℕ} (hjm : j < m) :
    ex55l_zeroB W (w.take m) j = ex55l_zeroB W w j := by
  unfold ex55l_zeroB
  refine Bool.eq_iff_iff.2 ?_
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  refine exists_congr fun k ↦ and_congr Iff.rfl ?_
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    rwa [List.take_take, min_eq_left (by omega)] at h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    rwa [List.take_take, min_eq_left (by omega)]

/-- The word map is monotone: `F(w↾m) = F(w)↾m`. -/
lemma ex55l_take_F (w : List Bool) (m : ℕ) (hm : m ≤ w.length) :
    ex55l_F W (w.take m) = (ex55l_F W w).take m := by
  refine List.ext_getElem (by simp [ex55l_F, hm]) fun j h1 h2 ↦ ?_
  have hj : j < m := by simpa [ex55l_F, hm] using h1
  simp only [ex55l_F, List.getElem_map, List.getElem_range, List.getElem_take]
  rw [ex55l_zeroB_take W w hj]
  congr 1
  simp [List.getD_eq_getElem?_getD, hj]

/-- The sequence map `f'` of Example 5.5(2). -/
def ex55l_f (y : ℕ → Bool) : ℕ → Bool := CantorPres.seqMap (ex55l_F W) y

/-- The sequence map is computed on prefixes by the word map. -/
lemma ex55l_wordPrefix_f (y : ℕ → Bool) (n : ℕ) :
    wordPrefix (ex55l_f W y) n = ex55l_F W (wordPrefix y n) :=
  cantorPres_wordPrefix_seqMap (ex55l_length_F W) (fun w k hk ↦ ex55l_take_F W w k hk) y n

/-- The sequence map, pointwise. -/
lemma ex55l_f_apply (y : ℕ → Bool) (j : ℕ) :
    ex55l_f W y j = (y j && !ex55l_zeroB W (wordPrefix y (j + 1)) j) := by
  unfold ex55l_f CantorPres.seqMap ex55l_F
  have hl : (wordPrefix y (j + 1)).length = j + 1 := by simp [wordPrefix]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hl, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [ex55l_getD_wordPrefix y (by omega)]

/-- On a block `J_k` with `y ∈ E_k`, the image vanishes. -/
lemma ex55l_f_of_in {y : ℕ → Bool} {k j : ℕ} (hy : ex55l_In W k y) (h1 : ex55l_N k ≤ j)
    (h2 : j < ex55l_N (k + 1)) : ex55l_f W y j = false := by
  have hz : ex55l_zeroB W (wordPrefix y (j + 1)) j = true :=
    (ex55l_zeroB_wordPrefix W y (Nat.lt_succ_self j)).2 ⟨k, h1, h2, hy⟩
  rw [ex55l_f_apply, hz]
  simp

/-- On a block `J_k` with `y ∉ E_k`, the image copies `y`. -/
lemma ex55l_f_of_not_in {y : ℕ → Bool} {k j : ℕ} (hy : ¬ ex55l_In W k y) (h1 : ex55l_N k ≤ j)
    (h2 : j < ex55l_N (k + 1)) : ex55l_f W y j = y j := by
  have hz : ex55l_zeroB W (wordPrefix y (j + 1)) j = false := by
    refine Bool.eq_false_iff.2 fun h ↦ ?_
    obtain ⟨k', h1', h2', hk'⟩ := (ex55l_zeroB_wordPrefix W y (Nat.lt_succ_self j)).1 h
    exact hy (ex55l_block_unique h1 h2 h1' h2' ▸ hk')
  rw [ex55l_f_apply, hz]
  simp

/-! ### Computability -/

/-- The block boundaries are primitive recursive. -/
lemma ex55l_primrec_N : Primrec ex55l_N :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp Primrec.id Primrec.succ

variable {W}

/-- The trigger is computable. -/
lemma ex55l_computable_trig (hW : Computable₂ W) : Computable (ex55l_trig W) := by
  have hn : Computable fun k : ℕ ↦ k.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
  have ht : Computable fun k : ℕ ↦ k.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
  have hany : Computable fun k : ℕ ↦ (List.range k.unpair.1).any
      fun j ↦ !decide (W k.unpair.2 j = W (k.unpair.2 - 1) j) := by
    refine computable_list_any (Primrec.list_range.to_comp.comp hn) ?_
    exact (Primrec.not.to_comp.comp (primrec_decideEq.to_comp.comp
      (hW.comp (ht.comp Computable.fst) Computable.snd)
      (hW.comp (Primrec.nat_sub.to_comp.comp (ht.comp Computable.fst) (Computable.const 1))
        Computable.snd))).to₂
  exact Primrec.and.to_comp.comp (Primrec.nat_lt.decide.to_comp.comp hn ht)
    (Primrec.or.to_comp.comp (primrec_decideEq.to_comp.comp ht
      (Primrec.succ.to_comp.comp hn)) hany)

/-- The word test is computable. -/
lemma ex55l_computable_inB (hW : Computable₂ W) : Computable₂ (ex55l_inB W) := by
  have hn : Computable fun p : ℕ × List Bool ↦ p.1.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have ht : Computable fun p : ℕ × List Bool ↦ p.1.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).to_comp
  have hany : Computable fun p : ℕ × List Bool ↦ (List.range p.1.unpair.1).any
      fun j ↦ !decide (W p.1.unpair.2 j = p.2.getD j false) := by
    refine computable_list_any (Primrec.list_range.to_comp.comp hn) ?_
    exact (Primrec.not.to_comp.comp (primrec_decideEq.to_comp.comp
      (hW.comp (ht.comp Computable.fst) Computable.snd)
      ((Primrec.list_getD false).to_comp.comp (Computable.snd.comp Computable.fst)
        Computable.snd))).to₂
  exact (Primrec.and.to_comp.comp ((ex55l_computable_trig hW).comp Computable.fst)
    (Primrec.not.to_comp.comp hany)).to₂

/-- The zero test is computable. -/
lemma ex55l_computable_zeroB (hW : Computable₂ W) : Computable₂ (ex55l_zeroB W) := by
  have hN := ex55l_primrec_N.to_comp
  change Computable fun a : List Bool × ℕ ↦ ex55l_zeroB W a.1 a.2
  refine (computable_list_any (f := fun a : List Bool × ℕ ↦ List.range (a.2 + 1))
    (p := fun (a : List Bool × ℕ) (k : ℕ) ↦ (decide (ex55l_N k ≤ a.2) &&
      decide (a.2 < ex55l_N (k + 1))) && ex55l_inB W k (a.1.take (ex55l_N k)))
    (Primrec.list_range.to_comp.comp (Primrec.succ.to_comp.comp Computable.snd)) ?_).of_eq
    fun a ↦ rfl
  -- the predicate, as a function of `((w, j), k)`
  have hj : Computable fun q : (List Bool × ℕ) × ℕ ↦ q.1.2 :=
    Computable.snd.comp Computable.fst
  have hk : Computable fun q : (List Bool × ℕ) × ℕ ↦ q.2 := Computable.snd
  have hw : Computable fun q : (List Bool × ℕ) × ℕ ↦ q.1.1 :=
    Computable.fst.comp Computable.fst
  exact (Primrec.and.to_comp.comp
    (Primrec.and.to_comp.comp (Primrec.nat_le.decide.to_comp.comp (hN.comp hk) hj)
      (Primrec.nat_lt.decide.to_comp.comp hj (hN.comp (Primrec.succ.to_comp.comp hk))))
    ((ex55l_computable_inB hW).comp hk
      (Primrec.list_take.to_comp.comp (hN.comp hk) hw))).to₂

/-- The word map is computable. -/
lemma ex55l_computable_F (hW : Computable₂ W) : Computable (ex55l_F W) := by
  refine Computable.list_map (Primrec.list_range.comp Primrec.list_length).to_comp ?_
  exact (Primrec.and.to_comp.comp
    ((Primrec.list_getD false).to_comp.comp Computable.fst Computable.snd)
    (Primrec.not.to_comp.comp ((ex55l_computable_zeroB hW).comp Computable.fst
      Computable.snd))).to₂

/-! ### A Martin-Löf random sequence with computable stabilising approximations -/

/-- There is a Martin-Löf random sequence `Ω` (for the fair-coin measure) together with a
computable family `W t` of sequences whose bits stabilise to those of `Ω`. Here `Ω` is the binary
expansion of Chaitin's `Ω`, and `W t j` is bit `j` of the rational lower approximation `Ω_t`
read with `j + 1` bits. Blueprint node `meas:examples`. -/
theorem ex55l_exists_omega : ∃ (Ω : ℕ → Bool) (W : ℕ → ℕ → Bool),
    IsMartinLofRandom uniformMeasure Ω ∧ Computable₂ W ∧ ∀ j, ∀ᶠ t in atTop, W t j = Ω j := by
  obtain ⟨m, hm⟩ := exists_isUniversalSemimeasureNat
  obtain ⟨V, hV⟩ := exists_isOptimalConditional
  obtain ⟨w, hw, -⟩ := exists_cantorReal_eq (omegaReal_mem_Ioo hm).1 (omegaReal_mem_Ioo hm).2.le
  obtain ⟨D, hD, hDspec⟩ := exists_computable_cantorPrefix_of_ratApprox
  obtain ⟨q, C, hqc, hq0, hqmono, hqle, hqacc⟩ := exists_computable_ratApprox_le_BPlain hm hV
  have hrand : IsMartinLofRandomReal (cantorReal w) := by
    rw [hw]; exact isMartinLofRandomReal_omegaReal hm
  obtain ⟨c₁, hrun⟩ := exists_const_window_true_of_isMartinLofRandomReal hrand
  refine ⟨w, fun t j ↦ (D (j + 1) (q t)).getD j false, omega_binary_isMartinLofRandom hm hw,
    ?_, fun j ↦ ?_⟩
  · exact ((Primrec.list_getD false).to_comp.comp
      (hD.comp (Primrec.succ.to_comp.comp Computable.snd) (hqc.comp Computable.fst))
      Computable.snd).to₂
  set M := j + 1 + c₁ * Nat.log 2 (j + 1 + 2) + c₁ with hM
  refine eventually_atTop.2 ⟨BPlain V (M + C), fun t ht ↦ ?_⟩
  have hlt : cantorReal w < ((q t : ℚ) : ℝ) + 1 / 2 ^ M := by
    have h1 := hqacc M
    have h2 : ((q (BPlain V (M + C)) : ℚ) : ℝ) ≤ ((q t : ℚ) : ℝ) := by exact_mod_cast hqmono ht
    rw [hw]
    linarith
  have hDt := hDspec w (q t) (j + 1) M (hq0 t) (ne_ratCast_of_isMartinLofRandomReal hrand)
    (by rw [hw]; exact hqle t) hlt (hrun (j + 1))
  dsimp only
  rw [hDt]
  exact ex55l_getD_wordPrefix w (Nat.lt_succ_self j)

end Kolmogorov.PointToSet
