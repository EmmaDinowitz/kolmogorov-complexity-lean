/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness

/-!
# Block coding: the complexity of a generic sequence

The `limsup` half of input (I3) of the note *Orbit complexity of Martin-Löf random points
equals entropy* (V'yugin's bound), in the form needed there: if `ω` is generic for a
shift-invariant probability measure `ν` on `ℕ → Fin p` (the frequency of every word `w` in `ω`
tends to `ν[w]`), then `limsup_n K^A(ω↾n) / n ≤ h_ν(σ)` for every oracle `A`.

Proof (a fixed block code; the method of types of the sketch of Proposition 7.10(i) of the note
*Entropy of non-invariant measures* is not needed). Fix `k ≥ 1` and `ε > 0`, and let
`π(w) = ν[w]` on the words of length `k`; genericity alone gives `∑_w π(w) = 1`
(`sum_wordCylinder_toReal_eq_one`). Symbols are letters `inl a` and words `inr w`; they get
natural code lengths `ℓ` in units of `1/M` with Kraft sum `∑ 2^{-ℓ/M} < 1` and mean length
`∑_w π(w) ℓ(inr w)/M ≤ H_ν(ξ^k) + ε` (`exists_codeLengths`: the Shannon code of
`2^{-ε/2} π + δ`). The Kraft–Chaitin theorem, applied to the requests
`(g ↦ concatenation of the words of g, ⌊∑_{x ∈ g} ℓ x / M⌋ + c₀)` for all lists `g` of symbols
(total mass `≤ 2^{-c₀} ∑_N ρ^N < ∞`), bounds `K^A` of the concatenation by
`⌊∑ ℓ / M⌋ + c` (`exists_complexity_flatten_le`). Parse `ω↾n` at an offset `r < k` into `r`
letters, the aligned `k`-blocks and `< k` letters (`blockParse`). Averaging over `r` the aligned
positions cover each `j < n` at most once (`sum_offsets_le`), so some offset has block cost at
most `(1/k) ∑_{j<n} ℓ(ω↾[j, j + k)) = (1/k) ∑_w ℓ(w) #occ_n(w)`, and `#occ_n(w)/n → ν[w]` by
genericity. Hence eventually `K^A(ω↾n) ≤ n (H_ν(ξ^k)/k + ε)`
(`eventually_wordComplexity_le`), and the `limsup` is at most `inf_k H_ν(ξ^k)/k = h_ν(σ)`.
The invariance of `ν` is not used. The helper lemmas live in the namespace
`Kolmogorov.PointToSet.BlockCoding`.
Blueprint node `erg:block-coding`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

namespace BlockCoding

/-! ### Windows, occurrence counts and the parsing of a prefix -/

section words

variable {α : Type*}

/-- The window `ω↾[s, s + k)` of a sequence, as a word of length `k`.
Blueprint node `erg:block-coding`. -/
def blockWindow (ω : ℕ → α) (k s : ℕ) : Fin k → α :=
  fun i ↦ ω (s + i)

/-- The number `#{j < n | ω↾[j, j + k) = w}` of occurrences of the word `w` in `ω↾(n + k - 1)`
(sliding windows starting before `n`). Blueprint node `erg:block-coding`. -/
def blockCount [DecidableEq α] (ω : ℕ → α) (k n : ℕ) (w : Fin k → α) : ℕ :=
  ((Finset.range n).filter fun j ↦ blockWindow ω k j = w).card

/-- The occurrence set of `IsGenericPoint` has `blockCount` elements.
Blueprint node `erg:block-coding`. -/
theorem ncard_occurrences_eq_blockCount [DecidableEq α] (ω : ℕ → α) {k : ℕ} (n : ℕ)
    (w : Fin k → α) :
    (({j | j < n ∧ ∀ i : Fin k, ω (j + i) = w i} : Set ℕ).ncard) = blockCount ω k n w := by
  rw [blockCount, ← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [blockWindow, funext_iff]

/-- Grouping the windows by their value: `∑_{j < n} h(ω↾[j, j + k)) = ∑_w h(w) #occ(w)`.
Blueprint node `erg:block-coding`. -/
theorem sum_range_blockWindow [Fintype α] [DecidableEq α] (ω : ℕ → α) (k n : ℕ)
    (h : (Fin k → α) → ℕ) :
    ∑ j ∈ Finset.range n, h (blockWindow ω k j) = ∑ w, h w * blockCount ω k n w := by
  rw [← Finset.sum_fiberwise (Finset.range n) (blockWindow ω k)]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.sum_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2], Finset.sum_const,
    smul_eq_mul, mul_comm, blockCount]

/-- The decoding map of the block code: a symbol `inl a` stands for the letter `a`, a symbol
`inr w` for the word `w`. Blueprint node `erg:block-coding`. -/
def blockOut {k : ℕ} : α ⊕ (Fin k → α) → List α :=
  Sum.elim (fun a ↦ [a]) fun w ↦ List.ofFn w

/-- `blockOut` on a letter. Blueprint node `erg:block-coding`. -/
@[simp] theorem blockOut_inl {k : ℕ} (a : α) :
    blockOut (Sum.inl a : α ⊕ (Fin k → α)) = [a] := rfl

/-- `blockOut` on a word. Blueprint node `erg:block-coding`. -/
@[simp] theorem blockOut_inr {k : ℕ} (w : Fin k → α) :
    blockOut (Sum.inr w : α ⊕ (Fin k → α)) = List.ofFn w := rfl

/-- The parsing of `ω↾n` at offset `r`: the first `r` letters one by one, then the
`⌊(n - r)/k⌋` aligned blocks `ω↾[r + i k, r + (i + 1) k)`, then the remaining letters one by
one. Blueprint node `erg:block-coding`. -/
def blockParse (ω : ℕ → α) (k r n : ℕ) : List (α ⊕ (Fin k → α)) :=
  (List.range r).map (fun i ↦ Sum.inl (ω i)) ++
    ((List.range ((n - r) / k)).map (fun i ↦ Sum.inr (blockWindow ω k (r + i * k))) ++
      (List.range (n - r - (n - r) / k * k)).map fun i ↦ Sum.inl (ω (r + (n - r) / k * k + i)))

/-- `List.ofFn` of a function of the index is a `map` over `List.range`.
Blueprint node `erg:block-coding`. -/
theorem ofFn_eq_map_range (f : ℕ → α) (n : ℕ) :
    List.ofFn (fun i : Fin n ↦ f i) = (List.range n).map f := by
  apply List.ext_getElem <;> simp

/-- Decoding singletons: `[f 0] ++ ⋯ ++ [f (m - 1)] = (f 0, …, f (m - 1))`.
Blueprint node `erg:block-coding`. -/
theorem flatten_map_blockOut_inl {k : ℕ} (f : ℕ → α) (m : ℕ) :
    (((List.range m).map fun i ↦ (Sum.inl (f i) : α ⊕ (Fin k → α))).map blockOut).flatten =
      (List.range m).map f := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.flatten_append, ih]
    simp

/-- Decoding aligned blocks: the blocks `ω↾[s + i k, s + (i + 1) k)`, `i < m`, concatenate to
`ω↾[s, s + m k)`. Blueprint node `erg:block-coding`. -/
theorem flatten_map_blockOut_inr (ω : ℕ → α) (k s m : ℕ) :
    (((List.range m).map fun i ↦
        (Sum.inr (blockWindow ω k (s + i * k)) : α ⊕ (Fin k → α))).map blockOut).flatten =
      (List.range (m * k)).map fun j ↦ ω (s + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.flatten_append, ih,
      Nat.succ_mul, List.range_add, List.map_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      blockOut_inr, List.map_map]
    congr 1
    rw [show blockWindow ω k (s + m * k) = fun i : Fin k ↦ ω (s + m * k + i) from rfl,
      ofFn_eq_map_range (fun j ↦ ω (s + m * k + j))]
    simp only [Function.comp_def, add_assoc]

/-- Decoding the parsing of `ω↾n` at an offset `r ≤ n` gives back `ω↾n`.
Blueprint node `erg:block-coding`. -/
theorem flatten_map_blockOut_blockParse (ω : ℕ → α) {k r n : ℕ} (hr : r ≤ n) :
    ((blockParse ω k r n).map blockOut).flatten = wordPrefix ω n := by
  have hn : n = r + ((n - r) / k * k + (n - r - (n - r) / k * k)) := by
    have := Nat.div_mul_le_self (n - r) k
    omega
  rw [blockParse, List.map_append, List.map_append, List.flatten_append, List.flatten_append,
    flatten_map_blockOut_inl, flatten_map_blockOut_inr, flatten_map_blockOut_inl, wordPrefix,
    ofFn_eq_map_range ω n]
  conv_rhs => rw [hn, List.range_add, List.range_add]
  simp only [List.map_append, List.map_map, Function.comp_def, add_assoc]

/-- A sum along `List.range` is a `Finset.range` sum. Blueprint node `erg:block-coding`. -/
theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The cost of the parsing at offset `r < k`: the at most `2k` single letters cost at most
`Λ = ∑_a ℓ(inl a)` each. Blueprint node `erg:block-coding`. -/
theorem sum_map_blockParse_le [Fintype α] (ω : ℕ → α) {k r : ℕ} (hr : r < k) (n : ℕ)
    (ℓ : α ⊕ (Fin k → α) → ℕ) :
    ((blockParse ω k r n).map ℓ).sum ≤ 2 * k * ∑ a, ℓ (Sum.inl a) +
      ∑ i ∈ Finset.range ((n - r) / k), ℓ (Sum.inr (blockWindow ω k (r + i * k))) := by
  set Λ := ∑ a, ℓ (Sum.inl a)
  have hΛ : ∀ a, ℓ (Sum.inl a) ≤ Λ := fun a ↦
    Finset.single_le_sum (f := fun a ↦ ℓ (Sum.inl a)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ a)
  have hsingle : ∀ (m : ℕ) (f : ℕ → α), ∑ i ∈ Finset.range m, ℓ (Sum.inl (f i)) ≤ m * Λ := by
    intro m f
    simpa using Finset.sum_le_card_nsmul (Finset.range m) _ Λ fun i _ ↦ hΛ (f i)
  have hk : 0 < k := by omega
  have ht : n - r - (n - r) / k * k < k := by
    have h1 := Nat.div_add_mod' (n - r) k
    have h2 := Nat.mod_lt (n - r) hk
    omega
  rw [blockParse, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.map_map, List.map_map, List.map_map, sum_map_range, sum_map_range, sum_map_range]
  have h1 := hsingle r ω
  have h2 := hsingle (n - r - (n - r) / k * k) fun i ↦ ω (r + (n - r) / k * k + i)
  simp only [Function.comp_def] at h1 h2 ⊢
  have h3 : r * Λ + (n - r - (n - r) / k * k) * Λ ≤ 2 * k * Λ := by
    rw [← add_mul]
    exact Nat.mul_le_mul_right Λ (by omega)
  omega

end words

/-- Averaging over the offsets: the aligned positions `r + i k` (`r < k`, `i < ⌊(n - r)/k⌋`)
are distinct and smaller than `n`. Blueprint node `erg:block-coding`. -/
theorem sum_offsets_le (f : ℕ → ℕ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ∑ r ∈ Finset.range k, ∑ i ∈ Finset.range ((n - r) / k), f (r + i * k) ≤
      ∑ j ∈ Finset.range n, f j := by
  rw [Finset.sum_sigma']
  have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ ↦ x.1 + x.2 * k)
      ((Finset.range k).sigma fun r ↦ Finset.range ((n - r) / k)) := by
    rintro ⟨r, i⟩ hri ⟨r', i'⟩ hri' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_range, Set.mem_Iio] at hri hri'
    simp only at heq
    have hr : r = r' := by
      have h1 := congrArg (· % k) heq
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hri.1,
        Nat.mod_eq_of_lt hri'.1] at h1
      exact h1
    subst hr
    have hi : i = i' := Nat.eq_of_mul_eq_mul_right hk (by omega)
    subst hi
    rfl
  rw [← Finset.sum_image (f := f) hinj]
  refine Finset.sum_le_sum_of_subset fun j hj ↦ ?_
  obtain ⟨⟨r, i⟩, hri, rfl⟩ := Finset.mem_image.mp hj
  simp only [Finset.mem_sigma, Finset.mem_range] at hri
  have h1 : (i + 1) * k ≤ (n - r) / k * k := Nat.mul_le_mul_right k hri.2
  have h2 : (n - r) / k * k ≤ n - r := Nat.div_mul_le_self _ _
  rw [Finset.mem_range]
  simp only [add_mul, one_mul] at h1
  change r + i * k < n
  omega

/-! ### Code lengths -/

/-- Code lengths in units of `1/M` for a sub-probability vector `π` on a finite set: a Kraft sum
`< 1` and a mean length at most the Shannon entropy plus `ε`. Blueprint node `erg:block-coding`.
-/
theorem exists_codeLengths {Γ : Type*} [Fintype Γ] (π : Γ → ℝ) (hπ0 : ∀ x, 0 ≤ π x)
    (hπ1 : ∑ x, π x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ ∃ ℓ : Γ → ℕ, ∑ x, (2 : ℝ) ^ (-(ℓ x : ℝ) / M) < 1 ∧
      ∑ x, π x * ℓ x / M ≤ ∑ x, -π x * Real.logb 2 (π x) + ε := by
  -- the code of `q = 2^{-ε/2} π + δ`, with `δ > 0` small, in units of `1/M`, `M ≥ 2/ε`
  set a : ℝ := (2 : ℝ) ^ (-(ε / 2)) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hloga : Real.logb 2 a = -(ε / 2) := by
    rw [ha, Real.logb_rpow two_pos (by norm_num)]
  set N : ℝ := Fintype.card Γ + 1 with hN
  have hN0 : 0 < N := by positivity
  set δ : ℝ := (1 - a) / (2 * N) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  set q : Γ → ℝ := fun x ↦ a * π x + δ with hq
  have hq0 : ∀ x, 0 < q x := fun x ↦ by have := hπ0 x; positivity
  have hsumq : ∑ x, q x < 1 := by
    have hcard : (Fintype.card Γ : ℝ) * δ < 1 - a := by
      rw [hδ, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    have hsum : ∑ x, q x = a * ∑ x, π x + Fintype.card Γ * δ := by
      simp [hq, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    nlinarith
  have hq1 : ∀ x, q x ≤ 1 := fun x ↦
    (Finset.single_le_sum (fun y _ ↦ (hq0 y).le) (Finset.mem_univ x)).trans hsumq.le
  set M : ℕ := ⌈2 / ε⌉₊ + 1 with hM
  have hM0 : 0 < M := Nat.succ_pos _
  have hMε : 1 / (M : ℝ) ≤ ε / 2 := by
    have h1 : 2 / ε ≤ (M : ℝ) := by
      rw [hM]
      push_cast
      linarith [Nat.le_ceil (2 / ε)]
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε] at h1
    nlinarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM0
  set ℓ : Γ → ℕ := fun x ↦ ⌈(M : ℝ) * -Real.logb 2 (q x)⌉₊ with hℓ
  have hlogq : ∀ x, 0 ≤ -Real.logb 2 (q x) := fun x ↦
    neg_nonneg.mpr (Real.logb_nonpos one_lt_two (hq0 x).le (hq1 x))
  refine ⟨M, hM0, ℓ, ?_, ?_⟩
  · refine lt_of_le_of_lt (Finset.sum_le_sum fun x _ ↦ ?_) hsumq
    have h1 : (M : ℝ) * -Real.logb 2 (q x) ≤ ℓ x := Nat.le_ceil _
    have h2 : -(ℓ x : ℝ) / M ≤ Real.logb 2 (q x) := by
      rw [div_le_iff₀ hMpos]
      linarith
    calc (2 : ℝ) ^ (-(ℓ x : ℝ) / M) ≤ (2 : ℝ) ^ Real.logb 2 (q x) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two h2
      _ = q x := Real.rpow_logb two_pos (by norm_num) (hq0 x)
  · have hterm : ∀ x, π x * ℓ x / M ≤ -π x * Real.logb 2 (π x) + ε * π x := by
      intro x
      rcases (hπ0 x).eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
      have h1 : (ℓ x : ℝ) < (M : ℝ) * -Real.logb 2 (q x) + 1 := Nat.ceil_lt_add_one (by
        have := hlogq x
        positivity)
      have h2 : Real.logb 2 (a * π x) ≤ Real.logb 2 (q x) :=
        Real.logb_le_logb_of_le one_lt_two (by positivity) (by simp only [hq]; linarith)
      rw [Real.logb_mul ha0.ne' hpos.ne', hloga] at h2
      have h3 : (ℓ x : ℝ) / M ≤ -Real.logb 2 (π x) + ε := by
        rw [div_le_iff₀ hMpos]
        have h4 : 1 ≤ ε / 2 * M := by rwa [div_le_iff₀ hMpos] at hMε
        nlinarith
      calc π x * ℓ x / M = π x * ((ℓ x : ℝ) / M) := by ring
        _ ≤ π x * (-Real.logb 2 (π x) + ε) := mul_le_mul_of_nonneg_left h3 hpos.le
        _ = -π x * Real.logb 2 (π x) + ε * π x := by ring
    calc ∑ x, π x * ℓ x / M ≤ ∑ x, (-π x * Real.logb 2 (π x) + ε * π x) :=
          Finset.sum_le_sum fun x _ ↦ hterm x
      _ = ∑ x, -π x * Real.logb 2 (π x) + ε * ∑ x, π x := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ∑ x, -π x * Real.logb 2 (π x) + ε := by nlinarith

/-! ### The coding theorem for concatenations -/

/-- A finite code with lengths `ℓ / M` of Kraft sum `< 1`, used for concatenations: the
concatenation of the words `out x` along a list `g` of symbols has complexity at most
`⌊(∑_{x ∈ g} ℓ x) / M⌋ + c`. Blueprint node `erg:block-coding`. -/
theorem exists_complexity_flatten_le {Γ β : Type} [Fintype Γ] [Primcodable Γ] [Primcodable β]
    (A : Set ℕ) (out : Γ → List β) (ℓ : Γ → ℕ) {M : ℕ} (hM : 0 < M)
    (hK : ∑ x, (2 : ℝ) ^ (-(ℓ x : ℝ) / M) < 1) :
    ∃ c : ℕ, ∀ g : List Γ,
      oracleComplexity A (natBits (Encodable.encode (g.map out).flatten)) ≤
        (g.map ℓ).sum / M + c := by
  classical
  -- the weights `u x = 2^{-ℓ(x)/M}` and their sum `ρ < 1`
  set u : Γ → ℝ≥0∞ := fun x ↦ (2 : ℝ≥0∞) ^ (-(ℓ x : ℝ) / M) with hu
  set ρ : ℝ≥0∞ := ∑ x, u x with hρdef
  have hρ : ρ < 1 := by
    have h : ρ = ENNReal.ofReal (∑ x, (2 : ℝ) ^ (-(ℓ x : ℝ) / M)) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity, hρdef]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hu, ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [h]
    exact ENNReal.ofReal_lt_one.mpr hK
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, (1 - ρ)⁻¹ ≤ 2 ^ c₀ := by
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt
      (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hρ).ne')
    refine ⟨m, hm.le.trans ?_⟩
    exact_mod_cast (Nat.lt_two_pow_self).le
  -- the request stream
  set cost : List Γ → ℕ := fun g ↦ (g.map ℓ).sum / M + 1 + c₀ with hcost
  set req : ℕ → Option (BitString × ℕ) := fun j ↦
    (Encodable.decode₂ (List Γ) j).map fun g ↦
      (natBits (Encodable.encode (g.map out).flatten), cost g) with hreqdef
  have hreq : ComputableIn {charOracle A} req := by
    have hout : Primrec out := Primrec.dom_finite out
    have hℓ : Primrec ℓ := Primrec.dom_finite ℓ
    have hcode : Primrec fun g : List Γ ↦ natBits (Encodable.encode (g.map out).flatten) :=
      primrec_natBits.comp (Primrec.encode.comp
        (Primrec.list_flatten.comp (Primrec.list_map Primrec.id (hout.comp Primrec.snd).to₂)))
    have hsum : Primrec fun g : List Γ ↦ (g.map ℓ).sum :=
      (Primrec.list_foldr Primrec.id (Primrec.const 0)
        (Primrec.nat_add.comp (hℓ.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun g ↦ by
        induction g with
        | nil => rfl
        | cons x g ih =>
          simp only [id, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
          rw [ih]
    have hc : Primrec cost :=
      Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_div.comp hsum (Primrec.const M))
        (Primrec.const 1)) (Primrec.const c₀)
    exact (Primrec.option_map Primrec.decode₂
      ((hcode.pair hc).comp Primrec.snd).to₂).to_comp.computableIn
  -- the mass of the requests
  have hW : ∀ g : List Γ, (g.map u).prod = (2 : ℝ≥0∞) ^ (-((g.map ℓ).sum : ℝ) / M) := by
    intro g
    induction g with
    | nil => simp
    | cons x g ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, hu, ←
        ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      congr 1
      push_cast
      ring
  have hcost_le : ∀ g : List Γ,
      (2 : ℝ≥0∞)⁻¹ ^ cost g ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * (g.map u).prod := by
    intro g
    rw [hW, hcost, pow_add, mul_comm]
    gcongr
    rw [← ENNReal.inv_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_neg]
    refine ENNReal.rpow_le_rpow_of_exponent_le one_le_two ?_
    have h1 := Nat.lt_div_mul_add (a := (g.map ℓ).sum) hM
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hMpos]
    have h2 : ((g.map ℓ).sum : ℝ) < ((g.map ℓ).sum / M : ℕ) * M + M := by exact_mod_cast h1
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hlists : ∑' g : List Γ, (g.map u).prod ≤ (1 - ρ)⁻¹ := by
    have hsurj : Function.Surjective fun σ : Σ N : ℕ, Fin N → Γ ↦ List.ofFn σ.2 :=
      fun g ↦ ⟨⟨g.length, fun i ↦ g[i]⟩, List.ofFn_getElem⟩
    refine (ENNReal.tsum_le_tsum_comp_of_surjective hsurj _).trans (le_of_eq ?_)
    rw [ENNReal.tsum_sigma', ← ENNReal.tsum_geometric]
    refine tsum_congr fun N ↦ ?_
    rw [tsum_fintype, hρdef, ← Fin.prod_const, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  have hmass : oracleRequestMass req ≤ 1 := by
    have h1 : ∀ j, (req j).elim 0 (fun r ↦ (2 : ℝ≥0∞)⁻¹ ^ r.2) =
        ⨆ g ∈ Encodable.decode₂ (List Γ) j, (2 : ℝ≥0∞)⁻¹ ^ cost g := by
      intro j
      rcases h : Encodable.decode₂ (List Γ) j with _ | g <;> simp [hreqdef, h]
    rw [oracleRequestMass, tsum_congr h1,
      tsum_iSup_decode₂ (fun x : ℝ≥0∞ ↦ x) rfl fun g ↦ (2 : ℝ≥0∞)⁻¹ ^ cost g]
    calc ∑' g : List Γ, (2 : ℝ≥0∞)⁻¹ ^ cost g
        ≤ ∑' g : List Γ, (2 : ℝ≥0∞)⁻¹ ^ c₀ * (g.map u).prod := ENNReal.tsum_le_tsum hcost_le
      _ = (2 : ℝ≥0∞)⁻¹ ^ c₀ * ∑' g : List Γ, (g.map u).prod := ENNReal.tsum_mul_left
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * 2 ^ c₀ := by gcongr; exact hlists.trans hc₀
      _ = 1 := by
        rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  obtain ⟨c, hc⟩ := oracle_kraftChaitin_bound A req hreq hmass
  refine ⟨1 + c₀ + c, fun g ↦ ?_⟩
  have h := hc (Encodable.encode g) (natBits (Encodable.encode (g.map out).flatten)) (cost g)
    (by simp [hreqdef])
  simp only [hcost] at h
  omega

/-! ### Genericity -/

/-- At a generic point the masses of the cylinders of length `k` add up to one.
Blueprint node `erg:block-coding`. -/
theorem sum_wordCylinder_toReal_eq_one {p : ℕ} (ν : Measure (ℕ → Fin p)) {ω : ℕ → Fin p}
    (hω : IsGenericPoint ν ω) (k : ℕ) :
    ∑ w : Fin k → Fin p, (ν (wordCylinder w)).toReal = 1 := by
  have hlim : Tendsto (fun n : ℕ ↦ ∑ w : Fin k → Fin p, (blockCount ω k n w : ℝ) / n) atTop
      (𝓝 (∑ w : Fin k → Fin p, (ν (wordCylinder w)).toReal)) := by
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    simpa only [ncard_occurrences_eq_blockCount] using hω k w
  have hone : ∀ n : ℕ, 1 ≤ n → ∑ w : Fin k → Fin p, (blockCount ω k n w : ℝ) / n = 1 := by
    intro n hn
    have h := sum_range_blockWindow ω k n fun _ ↦ 1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, one_mul] at h
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [← Finset.sum_div, div_eq_one_iff_eq hn']
    exact_mod_cast h.symm
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr'
    (eventually_atTop.mpr ⟨1, fun n hn ↦ (hone n hn).symm⟩))

/-- The block-coding bound for a fixed block length `k ≥ 1`: eventually
`K^A(ω↾n) ≤ n (H_ν(ξ^k)/k + ε)`. Blueprint node `erg:block-coding`. -/
theorem eventually_wordComplexity_le {p : ℕ} (A : Set ℕ) (ν : Measure (ℕ → Fin p))
    {ω : ℕ → Fin p} (hω : IsGenericPoint ν ω) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (wordComplexity A ω n : ℝ) ≤ n * (blockEntropy ν k / k + ε) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- code lengths for the letters (mass `0`) and the words of length `k` (mass `ν[w]`)
  set πb : (Fin k → Fin p) → ℝ := fun w ↦ (ν (wordCylinder w)).toReal with hπb
  set π : Fin p ⊕ (Fin k → Fin p) → ℝ := Sum.elim (fun _ ↦ 0) πb with hπ
  have hπ0 : ∀ x, 0 ≤ π x := by
    rintro (a | w)
    · simp [hπ]
    · simp [hπ, hπb]
  have hπ1 : ∑ x, π x ≤ 1 := by
    simp [hπ, Fintype.sum_sum_type, hπb, sum_wordCylinder_toReal_eq_one ν hω k]
  obtain ⟨M, hM, ℓ, hK, hℓ⟩ := exists_codeLengths π hπ0 hπ1 (ε := k * ε / 2) (by positivity)
  have hℓb : ∑ w, πb w * ℓ (Sum.inr w) / M ≤ blockEntropy ν k + k * ε / 2 := by
    simpa [hπ, Fintype.sum_sum_type, blockEntropy, hπb] using hℓ
  obtain ⟨c, hc⟩ := exists_complexity_flatten_le A (blockOut (α := Fin p) (k := k)) ℓ hM hK
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  set Λ : ℕ := ∑ a, ℓ (Sum.inl a) with hΛ
  set cnt : ℕ → ℕ := fun n ↦ ∑ w, ℓ (Sum.inr w) * blockCount ω k n w with hcnt
  -- the bound at the best offset
  have hbound : ∀ n, k ≤ n → (wordComplexity A ω n : ℝ) ≤
      (cnt n : ℝ) / (k * M) + (((2 * k * Λ : ℕ) : ℝ) / M + c) := by
    intro n hn
    set f : ℕ → ℕ := fun j ↦ ℓ (Sum.inr (blockWindow ω k j)) with hf
    have havg := sum_offsets_le f hk n
    have hsumf : ∑ j ∈ Finset.range n, f j = cnt n :=
      sum_range_blockWindow ω k n fun w ↦ ℓ (Sum.inr w)
    obtain ⟨r, hr, hrle⟩ := Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hk⟩
      (f := fun r ↦ k * ∑ i ∈ Finset.range ((n - r) / k), f (r + i * k))
      (g := fun _ ↦ cnt n) (by
        rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul]
        exact Nat.mul_le_mul_left k (havg.trans hsumf.le))
    rw [Finset.mem_range] at hr
    have hKn := hc (blockParse ω k r n)
    rw [flatten_map_blockOut_blockParse ω (by omega : r ≤ n)] at hKn
    have hS := sum_map_blockParse_le ω hr n ℓ
    set S := ((blockParse ω k r n).map ℓ).sum with hSdef
    set T := ∑ i ∈ Finset.range ((n - r) / k), f (r + i * k) with hT
    have h1 : ((S / M : ℕ) : ℝ) ≤ (S : ℝ) / M := Nat.cast_div_le
    have h2 : (S : ℝ) ≤ ((2 * k * Λ : ℕ) : ℝ) + T := by exact_mod_cast hS
    have h3 : (k : ℝ) * T ≤ cnt n := by exact_mod_cast hrle
    have h4 : (T : ℝ) ≤ cnt n / k := by rw [le_div_iff₀ hk0]; linarith
    have hKr : (wordComplexity A ω n : ℝ) ≤ ((S / M : ℕ) : ℝ) + c := by exact_mod_cast hKn
    calc (wordComplexity A ω n : ℝ) ≤ (S : ℝ) / M + c := by linarith
      _ ≤ (((2 * k * Λ : ℕ) : ℝ) + cnt n / k) / M + c := by gcongr; linarith
      _ = (cnt n : ℝ) / (k * M) + (((2 * k * Λ : ℕ) : ℝ) / M + c) := by
        field_simp
        ring
  -- asymptotics of the occurrence counts
  set Lstar : ℝ := ∑ w, (ℓ (Sum.inr w) : ℝ) * πb w with hLstar
  have hF : Tendsto (fun n : ℕ ↦ (cnt n : ℝ) / n) atTop (𝓝 Lstar) := by
    have h : Tendsto (fun n : ℕ ↦ ∑ w, (ℓ (Sum.inr w) : ℝ) * ((blockCount ω k n w : ℝ) / n))
        atTop (𝓝 Lstar) := by
      refine tendsto_finsetSum _ fun w _ ↦ Tendsto.const_mul _ ?_
      simpa only [ncard_occurrences_eq_blockCount] using hω k w
    refine h.congr fun n ↦ ?_
    simp only [hcnt, Nat.cast_sum, Nat.cast_mul, Finset.sum_div, mul_div_assoc]
  have hLk : Lstar / (k * M) ≤ blockEntropy ν k / k + ε / 2 := by
    have h : Lstar / M ≤ blockEntropy ν k + k * ε / 2 := by
      calc Lstar / M = ∑ w, πb w * ℓ (Sum.inr w) / M := by
            rw [hLstar, Finset.sum_div]
            exact Finset.sum_congr rfl fun w _ ↦ by ring
        _ ≤ _ := hℓb
    rw [mul_comm, ← div_div]
    calc Lstar / M / k ≤ (blockEntropy ν k + k * ε / 2) / k :=
          div_le_div_of_nonneg_right h hk0.le
      _ = blockEntropy ν k / k + ε / 2 := by field_simp
  have hkM : (0 : ℝ) < k * M := by positivity
  have hev1 : ∀ᶠ n : ℕ in atTop, (cnt n : ℝ) / n ≤ Lstar + ε / 4 * (k * M) :=
    hF.eventually (Iic_mem_nhds (by nlinarith))
  set C : ℝ := ((2 * k * Λ : ℕ) : ℝ) / M + c with hC
  have hev2 : ∀ᶠ n : ℕ in atTop, C ≤ n * (ε / 4) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (C / (ε / 4))] with n hn
    rwa [div_le_iff₀ (by positivity)] at hn
  filter_upwards [hev1, hev2, eventually_ge_atTop k, eventually_ge_atTop 1] with n hn1 hn2 hn3 hn4
  have hn : (0 : ℝ) < n := by exact_mod_cast hn4
  have hb := hbound n hn3
  have hcntle : (cnt n : ℝ) ≤ n * (Lstar + ε / 4 * (k * M)) := by
    rwa [div_le_iff₀ hn, mul_comm] at hn1
  have h5 : (cnt n : ℝ) / (k * M) ≤ n * (Lstar / (k * M) + ε / 4) := by
    rw [div_le_iff₀ hkM]
    calc (cnt n : ℝ) ≤ n * (Lstar + ε / 4 * (k * M)) := hcntle
      _ = n * (Lstar / (k * M) + ε / 4) * (k * M) := by field_simp
  calc (wordComplexity A ω n : ℝ) ≤ (cnt n : ℝ) / (k * M) + C := hb
    _ ≤ n * (Lstar / (k * M) + ε / 4) + n * (ε / 4) := by linarith
    _ ≤ n * (blockEntropy ν k / k + ε) := by nlinarith

end BlockCoding

/-- At a generic sequence of a shift-invariant measure on a finite alphabet,
`limsup_n K^A(ω↾n) / n ≤ h_ν(σ)` for every oracle `A`. Blueprint node `erg:block-coding`. -/
theorem limsup_wordComplexity_le_shiftEntropy {p : ℕ} (A : Set ℕ) (ν : Measure (ℕ → Fin p))
    [IsProbabilityMeasure ν] (hν : MeasurePreserving shiftMap ν ν) {ω : ℕ → Fin p}
    (hω : IsGenericPoint ν ω) :
    limsup (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop ≤ shiftEntropy ν := by
  -- the invariance of `ν` is not needed: genericity alone gives the bound
  have _ := hν
  refine le_iInf₂ fun k hk ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hev := BlockCoding.eventually_wordComplexity_le A ν hω hk (ε := ε) (by exact_mod_cast hε)
  calc limsup (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop
      ≤ ENNReal.ofReal (blockEntropy ν k / k + ε) := by
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (n := n),
          ← ENNReal.ofReal_div_of_pos hnpos]
        exact ENNReal.ofReal_le_ofReal ((div_le_iff₀' hnpos).mpr hn)
    _ ≤ ENNReal.ofReal (blockEntropy ν k / k) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (blockEntropy ν k / k) + ε := by rw [ENNReal.ofReal_coe_nnreal]

end Kolmogorov.PointToSet
