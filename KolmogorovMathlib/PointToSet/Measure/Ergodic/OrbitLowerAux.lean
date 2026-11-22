/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness
import Mathlib.Data.Set.Finite.List

/-!
# Coding lemmas for Theorem 1(b)

Step 4 of the proof of Theorem 1(b) of the note *Orbit complexity of Martin-Löf random points
equals entropy* (see `OrbitLower`): the word `ω↾n` is recovered from the index `i` of a
shadowing ideal point and the side information `v`, a list of length `n` with `v_k = some ω_k`
on the set `Bd` of bad times and `v_k = none` elsewhere.

* `orbitLower_decoder`: if `w` is compatible with `(i, v)` (for every `k`, either `v_k = some w_k`,
  or `v_k = none` and `T^k x_i ∈ U_{w_k}`), then `K^A(w) ≤ K^A(i) + K^A(v) + c`. The decoder
  searches for a compatible `w`: compatibility is `A`-r.e. (`T^k x_i` is uniformly computable
  and membership in an `A`-c.e. open set is semi-decidable), and the compatible `w` is unique
  because the `U_j` are disjoint.
* `orbitLower_optionList_bound`: for every `η > 0` there are `B ≥ 0` and `d` with
  `K^A(v) ≤ η |v| + B · #{k | v_k ≠ none} + d`. Proof: cut `v` into blocks of a large length
  `N`; a block without `some` is `none^N`, of complexity `≤ K^A(N) + O(1) = O(log N)`, any other
  block costs at most a constant `B_N`, and concatenation is subadditive up to a constant.

This replaces the explicit prefix-free encoding of the note (`n`, `|Bd|`, the index of `Bd`
among the subsets of its size, the symbols): only `K^A(v) ≤ o(1) n + O(θ n)` is needed.
Blueprint node `erg:theorem-one`.
-/

namespace Kolmogorov.PointToSet

open Filter Set

section graph

variable (A : Set ℕ)

/-- A functional `A`-r.e. graph on `k` input strings costs at most the sum of the complexities
of the inputs plus a constant. Blueprint node `erg:theorem-one`. -/
theorem orbitLower_complexity_le_of_graph (k : ℕ) {G : List BitString × BitString → Prop}
    (hG : IsREIn A G) (hfun : ∀ xs o o', G (xs, o) → G (xs, o') → o = o') :
    ∃ c : ℕ, ∀ xs o, xs.length = k → G (xs, o) →
      oracleComplexity A o ≤ (xs.map (oracleComplexity A)).sum + c := by
  obtain ⟨g, hg, hdom, hspec⟩ := hG.exists_partrecIn_choice
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A k g hg
  refine ⟨c, fun xs o hlen ho ↦ hc xs o hlen ?_⟩
  have hd : (g xs).Dom := (hdom xs).2 ⟨o, ho⟩
  have hmem : (g xs).get hd ∈ g xs := Part.get_mem hd
  have heq := hfun xs _ _ (hspec xs _ hmem) ho
  rw [← heq]
  exact hmem

/-- Equality of the values of two computable maps is a computable test. -/
private theorem computable_decide_eq {α β : Type*} [Primcodable α] [Primcodable β]
    [DecidableEq β] {f g : α → β} (hf : Computable f) (hg : Computable g) :
    Computable fun a ↦ decide (f a = g a) :=
  (Primrec.eq.decide.to_comp).comp hf hg

/-- The binary code `natBits (encode a)` is computable. -/
private theorem computable_code {α : Type*} [Primcodable α] :
    Computable fun a : α ↦ natBits (Encodable.encode a) :=
  natBits_computable.comp Computable.encode

/-- Two-element lists of computable strings are computable. -/
private theorem computable_pairList {α : Type*} [Primcodable α] {f g : α → BitString}
    (hf : Computable f) (hg : Computable g) : Computable fun a ↦ [f a, g a] :=
  (Primrec.list_cons.to_comp).comp hf
    ((Primrec.list_cons.to_comp).comp hg (Computable.const []))

/-- The code `natBits ∘ encode` is injective. -/
private theorem code_injective {α : Type*} [Primcodable α] {a b : α}
    (h : natBits (Encodable.encode a) = natBits (Encodable.encode b)) : a = b :=
  Encodable.encode_injective (natBits_injective h)

/-- A computable map of two arguments raises complexity by at most a constant:
`K^A(f(a, b)) ≤ K^A(a) + K^A(b) + c`. Blueprint node `erg:theorem-one`. -/
theorem orbitLower_complexity_map₂ {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] {f : α × β → γ} (hf : Computable f) :
    ∃ c : ℕ, ∀ a b, oracleComplexity A (natBits (Encodable.encode (f (a, b)))) ≤
      oracleComplexity A (natBits (Encodable.encode a)) +
        oracleComplexity A (natBits (Encodable.encode b)) + c := by
  classical
  let F : (List BitString × BitString) × (α × β) → Prop := fun q ↦
    q.1.1 = [natBits (Encodable.encode q.2.1), natBits (Encodable.encode q.2.2)] ∧
      q.1.2 = natBits (Encodable.encode (f q.2))
  have hF : IsREIn A F := by
    refine (isREIn_of_computable_decide ?_).and (isREIn_of_computable_decide ?_)
    · exact computable_decide_eq (Computable.fst.comp Computable.fst)
        (computable_pairList (computable_code.comp (Computable.fst.comp Computable.snd))
          (computable_code.comp (Computable.snd.comp Computable.snd)))
    · exact computable_decide_eq (Computable.snd.comp Computable.fst)
        (computable_code.comp (hf.comp Computable.snd))
  have hfun : ∀ xs o o', (∃ t, F ((xs, o), t)) → (∃ t, F ((xs, o'), t)) → o = o' := by
    intro xs o o' h h'
    obtain ⟨⟨a, b⟩, h₁, h₂⟩ := h
    obtain ⟨⟨a', b'⟩, h₁', h₂'⟩ := h'
    simp only at h₁ h₂ h₁' h₂'
    rw [h₁] at h₁'
    simp only [List.cons.injEq, and_true] at h₁'
    obtain ⟨ha, hb⟩ := h₁'
    rw [h₂, h₂', code_injective ha, code_injective hb]
  obtain ⟨c, hc⟩ := orbitLower_complexity_le_of_graph A 2 hF.exists
    (G := fun d ↦ ∃ t, F (d, t)) hfun
  refine ⟨c, fun a b ↦ ?_⟩
  have h := hc [natBits (Encodable.encode a), natBits (Encodable.encode b)]
    (natBits (Encodable.encode (f (a, b)))) rfl ⟨(a, b), rfl, rfl⟩
  simpa [add_assoc] using h

/-- A computable map of one argument raises complexity by at most a constant.
Blueprint node `erg:theorem-one`. -/
theorem orbitLower_complexity_map {α γ : Type*} [Primcodable α] [Primcodable γ] {f : α → γ}
    (hf : Computable f) :
    ∃ c : ℕ, ∀ a, oracleComplexity A (natBits (Encodable.encode (f a))) ≤
      oracleComplexity A (natBits (Encodable.encode a)) + c := by
  obtain ⟨c, hc⟩ := orbitLower_complexity_map₂ A (f := fun q : α × Unit ↦ f q.1)
    (hf.comp Computable.fst)
  refine ⟨c + oracleComplexity A (natBits (Encodable.encode ())), fun a ↦ ?_⟩
  have := hc a ()
  simp only at this
  omega

/-- Finitely many lists of bounded length have bounded complexity.
Blueprint node `erg:theorem-one`. -/
theorem orbitLower_complexity_bdd {α : Type*} [Primcodable α] [Finite α] (N : ℕ) :
    ∃ C : ℕ, ∀ v : List α, v.length ≤ N →
      oracleComplexity A (natBits (Encodable.encode v)) ≤ C := by
  obtain ⟨C, hC⟩ := ((List.finite_length_le α N).image
    fun v ↦ oracleComplexity A (natBits (Encodable.encode v))).bddAbove
  exact ⟨C, fun v hv ↦ hC ⟨v, hv, rfl⟩⟩

end graph

section blocks

/-- `log₂ y ≤ log₂ M + 2 y / M` for `y, M > 0`. -/
private theorem logb_le_add_div {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    Real.logb 2 y ≤ Real.logb 2 M + 2 * (y / M) := by
  have ht : 0 < y / M := div_pos hy hM
  have hsplit : Real.logb 2 y = Real.logb 2 M + Real.logb 2 (y / M) := by
    rw [Real.logb_div hy.ne' hM.ne']
    ring
  rw [hsplit]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (x := 2) two_pos
    norm_num at this ⊢
    linarith
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hle : Real.logb 2 (y / M) ≤ 2 * (y / M) := by
    rw [Real.logb]
    rcases le_or_gt (Real.log (y / M)) 0 with h | h
    · have : Real.log (y / M) / Real.log 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hlog2pos.le
      linarith
    · have h1 : Real.log (y / M) ≤ y / M - 1 := Real.log_le_sub_one_of_pos ht
      rw [div_le_iff₀ hlog2pos]
      nlinarith
  linarith

variable (A : Set ℕ) {β : Type*} [Primcodable β]

/-- The block estimate: with `κ ≥ K^A(none^N)`, `c_a` the concatenation constant and `K_max` a
bound for lists of length `≤ N`, `K^A(v) ≤ (|v|/N)(κ + c_a) + K_max (#some + 1)`. -/
private theorem complexity_blocks_aux {N : ℕ} (hN : 0 < N) {κ ca Kmax : ℝ} (hca : 0 ≤ ca)
    (hK0 : 0 ≤ Kmax)
    (happ : ∀ u v : List (Option β),
      (oracleComplexity A (natBits (Encodable.encode (u ++ v))) : ℝ) ≤
        oracleComplexity A (natBits (Encodable.encode u)) +
          oracleComplexity A (natBits (Encodable.encode v)) + ca)
    (hrep : (oracleComplexity A (natBits (Encodable.encode
      (List.replicate N (none : Option β)))) : ℝ) ≤ κ)
    (hsmall : ∀ v : List (Option β), v.length ≤ N →
      (oracleComplexity A (natBits (Encodable.encode v)) : ℝ) ≤ Kmax)
    (v : List (Option β)) :
    (oracleComplexity A (natBits (Encodable.encode v)) : ℝ) ≤
      (v.length / N : ℝ) * (κ + ca) + Kmax * v.countP Option.isSome + Kmax := by
  have hκ : 0 ≤ κ := le_trans (Nat.cast_nonneg _) hrep
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  induction h : v.length using Nat.strong_induction_on generalizing v with
  | _ m ih =>
  subst h
  rcases lt_or_ge v.length N with hm | hm
  · have h1 := hsmall v (by omega)
    have h2 : 0 ≤ (v.length / N : ℝ) * (κ + ca) := by positivity
    have h3 : 0 ≤ Kmax * (v.countP Option.isSome : ℝ) := by positivity
    linarith
  · set t := v.take N with ht
    set r := v.drop N with hr
    have hsplit : v = t ++ r := (List.take_append_drop N v).symm
    have hrlen : r.length < v.length := by
      simp only [hr, List.length_drop]
      omega
    have ih' := ih _ hrlen r rfl
    have htake : (oracleComplexity A (natBits (Encodable.encode t)) : ℝ) ≤
        κ + Kmax * t.countP Option.isSome := by
      by_cases hc : t.countP Option.isSome = 0
      · have htr : t = List.replicate N none := by
          rw [List.eq_replicate_iff]
          refine ⟨by simp only [ht, List.length_take]; omega, fun b hb ↦ ?_⟩
          rw [List.countP_eq_zero] at hc
          simpa using hc b hb
        rw [hc, htr]
        simpa using hrep
      · have h1 : (1 : ℝ) ≤ t.countP Option.isSome := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hc
        have h2 := hsmall t (by simp [ht])
        nlinarith
    have hcount : v.countP Option.isSome = t.countP Option.isSome + r.countP Option.isSome := by
      conv_lhs => rw [hsplit]
      exact List.countP_append
    have hlen : (v.length : ℝ) / N = 1 + (r.length : ℝ) / N := by
      have : (r.length : ℝ) = v.length - N := by
        simp only [hr, List.length_drop]
        rw [Nat.cast_sub (by omega)]
      rw [this]
      field_simp
      ring
    have happ' := happ t r
    rw [← hsplit] at happ'
    rw [hlen, hcount]
    push_cast
    nlinarith

/-- Option lists with few `some` entries have small complexity: for every `η > 0` there are
`B ≥ 0` and `d` with `K^A(v) ≤ η |v| + B · #{k | v_k ≠ none} + d`.
Blueprint node `erg:theorem-one`. -/
theorem orbitLower_optionList_bound [Finite β] {η : ℝ} (hη : 0 < η) :
    ∃ B d : ℝ, 0 ≤ B ∧ ∀ v : List (Option β),
      (oracleComplexity A (natBits (Encodable.encode v)) : ℝ) ≤
        η * v.length + B * v.countP Option.isSome + d := by
  obtain ⟨ca, hca⟩ := orbitLower_complexity_map₂ A
    (f := fun q : List (Option β) × List (Option β) ↦ q.1 ++ q.2)
    (Primrec.list_append.comp Primrec.fst Primrec.snd).to_comp
  obtain ⟨cr, hcr⟩ := orbitLower_complexity_map A
    (f := fun N : ℕ ↦ List.replicate N (none : Option β))
    (Primrec.list_replicate.comp Primrec.id (Primrec.const none)).to_comp
  obtain ⟨c₁, hc₁⟩ := oracleNatComplexity_le_log_add_loglog A
  -- choose the block length `N`
  set M : ℝ := 40 / η with hM
  have hMpos : 0 < M := by positivity
  set K₀ : ℝ := 5 * Real.logb 2 M + 4 + |c₁| + cr + ca with hK₀
  set N : ℕ := ⌈2 * K₀ / η⌉₊ + 1 with hNdef
  have hN : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNK : K₀ ≤ η * N / 2 := by
    have h1 : 2 * K₀ / η ≤ ⌈2 * K₀ / η⌉₊ := Nat.le_ceil _
    have h2 : (N : ℝ) = ⌈2 * K₀ / η⌉₊ + 1 := by simp [hNdef]
    have h3 : 2 * K₀ ≤ η * ⌈2 * K₀ / η⌉₊ := by
      rw [div_le_iff₀ hη] at h1
      linarith
    rw [h2]
    nlinarith
  -- the complexity of `none^N`
  set κ : ℝ := ((oracleComplexity A (natBits (Encodable.encode
    (List.replicate N (none : Option β)))) : ℕ) : ℝ) with hκ
  have hκN : κ + ca ≤ η * N := by
    have hrep := hcr N
    simp only [Encodable.encode_nat] at hrep
    have hlogN := hc₁ N
    set z : ℝ := Real.logb 2 ((N : ℝ) + 1) with hz
    have hz0 : 0 ≤ z := Real.logb_nonneg one_lt_two (by linarith)
    have hzz : Real.logb 2 (z + 1) ≤ 2 * (z + 1) := by
      have := logb_le_add_div (y := z + 1) (M := 1) (by linarith) one_pos
      simpa using this
    have hzM : z ≤ Real.logb 2 M + 2 * (((N : ℝ) + 1) / M) :=
      logb_le_add_div (by positivity) hMpos
    have hfrac : 2 * (((N : ℝ) + 1) / M) = η * (N + 1) / 20 := by
      rw [hM]
      field_simp
      ring
    have hκle : κ ≤ (oracleNatComplexity A N : ℝ) + cr := by
      simp only [hκ]
      exact_mod_cast hrep
    have hc₁abs : c₁ ≤ |c₁| := le_abs_self c₁
    nlinarith
  obtain ⟨C, hC⟩ := orbitLower_complexity_bdd A (α := Option β) N
  refine ⟨C, C, Nat.cast_nonneg _, fun v ↦ ?_⟩
  have hb := complexity_blocks_aux A hN (κ := κ) (ca := ca) (Kmax := C) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (fun u v ↦ by exact_mod_cast hca u v) le_rfl
    (fun v hv ↦ by exact_mod_cast hC v hv) v
  have hNr0 : (0 : ℝ) < N := by linarith
  have : (v.length / N : ℝ) * (κ + ca) ≤ η * v.length := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hNr0]
    have : (0 : ℝ) ≤ v.length := Nat.cast_nonneg _
    nlinarith
  linarith

end blocks

section decoder

variable {X : Type*} [MetricSpace X]

/-- The word `w` is compatible with the shadowing ideal point `x_i` and the side information
`v`: same length, and for every `k`, either `v_k = some w_k`, or `v_k = none` and
`T^k x_i ∈ U_{w_k}`. Blueprint node `erg:theorem-one`. -/
def OrbitLowerCompatible (P : Presentation X) (T : X → X) {p : ℕ} (U : Fin p → Set X)
    (i : ℕ) (v : List (Option (Fin p))) (w : List (Fin p)) : Prop :=
  w.length = v.length ∧ ∀ k (hk : k < w.length), v.getD k none = some (w.get ⟨k, hk⟩) ∨
    (v.getD k none = none ∧ T^[k] (P.ι i) ∈ U (w.get ⟨k, hk⟩))

/-- For a disjoint family the compatible word is unique. Blueprint node `erg:theorem-one`. -/
theorem OrbitLowerCompatible.unique {P : Presentation X} {T : X → X} {p : ℕ}
    {U : Fin p → Set X} (hdisj : Pairwise (Function.onFun Disjoint U)) {i : ℕ}
    {v : List (Option (Fin p))} {w w' : List (Fin p)} (h : OrbitLowerCompatible P T U i v w)
    (h' : OrbitLowerCompatible P T U i v w') : w = w' := by
  apply List.ext_get (h.1.trans h'.1.symm)
  intro k hk hk'
  rcases h.2 k hk with h1 | ⟨h1, h1'⟩ <;> rcases h'.2 k hk' with h2 | ⟨h2, h2'⟩
  · exact Option.some.inj (h1.symm.trans h2)
  · rw [h1] at h2
    exact absurd h2 (by simp)
  · rw [h1] at h2
    exact absurd h2 (by simp)
  · by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) h1' h2'

/-- Membership of the iterates of ideal points in a uniformly `A`-c.e. open family is `A`-r.e.,
uniformly in the index of the point, the time and the member of the family. -/
private theorem isREIn_iterate_mem {P : Presentation X} {T : X → X} {A : Set ℕ}
    (hP : ComputablePresentationIn P A) (hT : IsRepresentedMapIn P P A T) {p : ℕ}
    {U : Fin p → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsREIn A fun q : ℕ × ℕ × Fin p ↦ T^[q.2.1] (P.ι q.1) ∈ U q.2.2 := by
  obtain ⟨E, hE, hUeq⟩ := hU
  have hlt := birkhoff_computableIn_lt A _
    (isComputableRealFamilyIn_dist_iterate_ideal P T A hP hT)
  have h1 : IsREIn A fun d : (ℕ × ℕ × Fin p) × (ℕ × ℚ) ↦
      E (d.1.2.2, d.2) ∧ dist (T^[d.1.2.1] (P.ι d.1.1)) (P.ι d.2.1) < (d.2.2 : ℝ) := by
    refine (hE.comp (f := fun d : (ℕ × ℕ × Fin p) × (ℕ × ℚ) ↦ (d.1.2.2, d.2)) ?_).and
      (hlt.comp (f := fun d : (ℕ × ℕ × Fin p) × (ℕ × ℚ) ↦
        ((d.1.2.1, d.1.1, d.2.1), d.2.2)) ?_)
    · exact ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
        Computable.snd).computableIn
    · exact (((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        ((Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd))).pair
          (Computable.snd.comp Computable.snd)).computableIn
  have key : (fun q : ℕ × ℕ × Fin p ↦ T^[q.2.1] (P.ι q.1) ∈ U q.2.2) =
      fun q ↦ ∃ b : ℕ × ℚ, E (q.2.2, b) ∧
        dist (T^[q.2.1] (P.ι q.1)) (P.ι b.1) < (b.2 : ℝ) := by
    funext q
    rw [hUeq q.2.2]
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, basicBall, Metric.mem_ball]
  rw [key]
  exact h1.exists

/-- Step 4 of Theorem 1(b) (the decoder): a word compatible with `(i, v)` has complexity at most
`K^A(i) + K^A(v) + c`. Blueprint node `erg:theorem-one`. -/
theorem orbitLower_decoder (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hT : IsRepresentedMapIn P P A T) {p : ℕ}
    {U : Fin p → Set X} (hU : IsCeOpenFamilyIn P A U)
    (hdisj : Pairwise (Function.onFun Disjoint U)) :
    ∃ c : ℕ, ∀ (i : ℕ) (v : List (Option (Fin p))) (w : List (Fin p)),
      OrbitLowerCompatible P T U i v w →
      oracleComplexity A (natBits (Encodable.encode w)) ≤
        oracleNatComplexity A i + oracleComplexity A (natBits (Encodable.encode v)) + c := by
  classical
  have hmem := isREIn_iterate_mem hP hT hU
  have hF : IsREIn A fun d : (ℕ × List (Option (Fin p))) × ℕ × Fin p ↦
      d.1.2.getD d.2.1 none = some d.2.2 ∨
        (d.1.2.getD d.2.1 none = none ∧ T^[d.2.1] (P.ι d.1.1) ∈ U d.2.2) := by
    have hget : Computable fun d : (ℕ × List (Option (Fin p))) × ℕ × Fin p ↦
        d.1.2.getD d.2.1 none :=
      (Primrec.list_getD none).to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.snd)
    refine (isREIn_of_computable_decide ?_).or
      ((isREIn_of_computable_decide ?_).and (hmem.comp
        (f := fun d : (ℕ × List (Option (Fin p))) × ℕ × Fin p ↦ (d.1.1, d.2.1, d.2.2)) ?_))
    · exact computable_decide_eq hget (Computable.option_some.comp
        (Computable.snd.comp Computable.snd))
    · exact computable_decide_eq hget (Computable.const none)
    · exact ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp Computable.snd).pair
          (Computable.snd.comp Computable.snd))).computableIn
  have hcomp : IsREIn A fun t : (ℕ × List (Option (Fin p))) × List (Fin p) ↦
      OrbitLowerCompatible P T U t.1.1 t.1.2 t.2 :=
    (isREIn_of_computable_decide (P := fun t : (ℕ × List (Option (Fin p))) × List (Fin p) ↦
      t.2.length = t.1.2.length) (computable_decide_eq
        (Primrec.list_length.to_comp.comp Computable.snd)
        (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst)))).and
      hF.list_forall_get
  let G : (List BitString × BitString) × ((ℕ × List (Option (Fin p))) × List (Fin p)) →
      Prop := fun q ↦ (q.1.1 = [natBits q.2.1.1, natBits (Encodable.encode q.2.1.2)] ∧
      q.1.2 = natBits (Encodable.encode q.2.2)) ∧
        OrbitLowerCompatible P T U q.2.1.1 q.2.1.2 q.2.2
  have hG : IsREIn A G := by
    refine ((isREIn_of_computable_decide ?_).and (isREIn_of_computable_decide ?_)).and
      (hcomp.comp Computable.snd.computableIn)
    · exact computable_decide_eq (Computable.fst.comp Computable.fst)
        (computable_pairList
          (natBits_computable.comp (Computable.fst.comp (Computable.fst.comp Computable.snd)))
          (computable_code.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))))
    · exact computable_decide_eq (Computable.snd.comp Computable.fst)
        (computable_code.comp (Computable.snd.comp Computable.snd))
  have hfun : ∀ xs o o', (∃ t, G ((xs, o), t)) → (∃ t, G ((xs, o'), t)) → o = o' := by
    intro xs o o' h h'
    obtain ⟨⟨⟨i, v⟩, w⟩, ⟨h₁, h₂⟩, h₃⟩ := h
    obtain ⟨⟨⟨i', v'⟩, w'⟩, ⟨h₁', h₂'⟩, h₃'⟩ := h'
    simp only at h₁ h₂ h₃ h₁' h₂' h₃'
    rw [h₁] at h₁'
    simp only [List.cons.injEq, and_true] at h₁'
    obtain ⟨hi, hv⟩ := h₁'
    obtain rfl := natBits_injective hi
    obtain rfl := code_injective hv
    rw [h₂, h₂', h₃.unique hdisj h₃']
  obtain ⟨c, hc⟩ := orbitLower_complexity_le_of_graph A 2 hG.exists
    (G := fun d ↦ ∃ t, G (d, t)) hfun
  refine ⟨c, fun i v w hw ↦ ?_⟩
  have h := hc [natBits i, natBits (Encodable.encode v)] (natBits (Encodable.encode w)) rfl
    ⟨((i, v), w), ⟨rfl, rfl⟩, hw⟩
  simpa [oracleNatComplexity, add_assoc] using h

end decoder

end Kolmogorov.PointToSet
