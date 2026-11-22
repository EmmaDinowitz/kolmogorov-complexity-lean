/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.TypicalPoints
import KolmogorovMathlib.PointToSet.Measure.Ergodic.SymbolicLowerBound
import KolmogorovMathlib.Ergodic.FinePartitions
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitLowerAux

/-!
# Theorem 1(b): the lower bound

Theorem 1(b) of the note *Orbit complexity of Martin-Löf random points equals entropy*: on a
compact space, for an `A`-represented ergodic map `T` and an `A`-computable invariant probability
measure `μ`, at every `μ`-random point `x` relative to `A`: for every `H < h_μ(T)` there is
`ε₀ > 0` with `liminf_n K_n^A(x, T, ε) / n ≥ H` for all `0 < ε ≤ ε₀`.

Proof (§4(b) of the note, with a cruder but sufficient coding in Step 4).
1. Partition: by Lemma 2 and (I4) (`lt_entropyRate_of_diam_lt`) fix `U_1, …, U_p` whose
   measurable partition `Q` has `h_μ(T, Q) > H₁ > H`; put `η = H₁ - H`.
2. (`exists_ballUnion_shadow`) The basic balls `B(x_c, q)` with `B(x_c, 2q) ⊆ U_j` for some `j`
   cover `⋃ U_j`; a finite union `V` of them has `μ(V) > 1 - θ`, and with `δ₀` the least
   radius used: if `y ∈ V` and `d(y, z) < δ₀` then `y, z` lie in the same `U_j`. `V` is
   `A`-c.e. open (`ballUnion_ceOpen`).
3. (`eventually_card_bad_le`) By (I2′) (`measure_le_liminf_visitFrequency`),
   `#{k < n | T^k x ∉ V} ≤ θ n` for all large `n`.
4. For `0 < ε ≤ δ₀` and `i` realizing `K_n^A(x, T, ε)`, the word `ω↾n` (`ω = φ(x)`) is
   computed from `i` and the side information `v ∈ (Option (Fin p))^n`, `v_k = some ω_k` for
   `k ∈ Bd = {k < n | T^k x ∉ V}` and `v_k = none` otherwise: for `k ∉ Bd` search the `j` with
   `T^k x_i ∈ U_j` (`orbitLower_decoder` in `OrbitLowerAux`). So
   `K^A(ω↾n) ≤ K_n^A(x, T, ε) + K^A(v) + O(1)`, and `K^A(v) ≤ (η/4) n + B |Bd| + d`
   (`orbitLower_optionList_bound`, block coding of `v`). The note's bound
   `K^A(v) ≤ n(H₂(θ) + θ log₂ p) + O(log n)` is not needed: `θ` is chosen with `B θ ≤ η/4`.
5. `liminf_n K^A(ω↾n)/n ≥ h_ν(σ) = h_μ(T, Q) > H₁` (`shiftEntropy_le_liminf_wordComplexity`,
   `symbolicCode_mem_wordRandomPoints`, `shiftEntropy_codedMeasure`), so eventually
   `K_n^A(x, T, ε) ≥ n (H₁ - η/2) - O(1) ≥ n H`.

Blueprint node `erg:theorem-one`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A ratio of natural numbers in `ℝ≥0∞` is the `ofReal` of the real ratio. -/
private theorem natCast_div_eq_ofReal (a : ℕ) {n : ℕ} (hn : 0 < n) :
    (a : ℝ≥0∞) / n = ENNReal.ofReal ((a : ℝ) / n) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hn), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

omit [CompactSpace X] in
/-- Step 2 of Theorem 1(b): a finite union `V` of basic balls of measure `> 1 - θ` and a radius
`δ₀ > 0` such that `δ₀`-close points `y ∈ V`, `z` lie in the same `U_j`. -/
private theorem exists_ballUnion_shadow (P : Presentation X) (μ : Measure X)
    [IsProbabilityMeasure μ] {p : ℕ} {U : Fin p → Set X} (hUo : ∀ j, IsOpen (U j))
    (hfull : μ (⋃ j, U j)ᶜ = 0) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (L : List (ℕ × ℚ)) (δ₀ : ℝ), 0 < δ₀ ∧ ENNReal.ofReal (1 - θ) < μ (ballUnion P L) ∧
      ∀ y ∈ ballUnion P L, ∀ z, dist y z < δ₀ → ∃ j, y ∈ U j ∧ z ∈ U j := by
  classical
  let G : Set (ℕ × ℚ) := {b | 0 < b.2 ∧ ∃ j, Metric.ball (P.ι b.1) (2 * b.2) ⊆ U j}
  let S : ℕ → Set (ℕ × ℚ) := fun N ↦ {b | b ∈ G ∧ Encodable.encode b < N}
  let W : ℕ → Set X := fun N ↦ ⋃ b ∈ S N, basicBall P b
  have hWmono : Monotone W := fun N N' h ↦
    biUnion_mono (fun b hb ↦ ⟨hb.1, lt_of_lt_of_le hb.2 h⟩) (fun _ _ ↦ subset_rfl)
  have hcover : (⋃ j, U j) ⊆ ⋃ N, W N := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hUo j) y hj
    obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (show (0 : ℝ) < r / 3 by positivity)
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp P.dense y q hq0
    refine mem_iUnion.mpr ⟨Encodable.encode (c, q) + 1, mem_iUnion₂.mpr
      ⟨(c, q), ⟨⟨by exact_mod_cast hq0, j, ?_⟩, by omega⟩, ?_⟩⟩
    · intro z hz
      apply hball
      rw [Metric.mem_ball] at hz ⊢
      have := dist_triangle z (P.ι c) y
      rw [dist_comm] at hc
      simp only at hz
      linarith
    · change y ∈ Metric.ball (P.ι c) (q : ℝ)
      rw [Metric.mem_ball]
      exact hc
  have hmeasU : MeasurableSet (⋃ j, U j) := MeasurableSet.iUnion fun j ↦ (hUo j).measurableSet
  have hU1 : μ (⋃ j, U j) = 1 := (prob_compl_eq_zero_iff hmeasU).mp hfull
  have h1 : μ (⋃ N, W N) = 1 :=
    le_antisymm prob_le_one (hU1 ▸ measure_mono hcover)
  have hlt : ENNReal.ofReal (1 - θ) < μ (⋃ N, W N) := by
    rw [h1, ENNReal.ofReal_lt_one]
    linarith
  obtain ⟨N, hN⟩ := ((tendsto_measure_iUnion_atTop (μ := μ) hWmono).eventually
    (lt_mem_nhds hlt)).exists
  have hfin : (S N).Finite :=
    ((Set.finite_lt_nat N).preimage Encodable.encode_injective.injOn).subset
      fun b hb ↦ hb.2
  let s := hfin.toFinset
  have hWL : W N = ballUnion P s.toList := by
    ext y
    simp only [W, ballUnion, Finset.mem_toList, s, Set.Finite.mem_toFinset]
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ b ∈ s, δ₀ ≤ (b.2 : ℝ) := by
    by_cases hs : s.Nonempty
    · refine ⟨s.inf' hs fun b ↦ (b.2 : ℝ), (Finset.lt_inf'_iff hs).2 fun b hb ↦ ?_,
        fun b hb ↦ Finset.inf'_le _ hb⟩
      have hb' : b ∈ S N := hfin.mem_toFinset.mp hb
      exact_mod_cast hb'.1.1
    · exact ⟨1, one_pos, fun b hb ↦ (hs ⟨b, hb⟩).elim⟩
  refine ⟨s.toList, δ₀, hδ₀, by simpa [Function.comp, hWL] using hN, fun y hy z hyz ↦ ?_⟩
  rw [← hWL] at hy
  obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy
  have hδb := hδ₀le b (hfin.mem_toFinset.mpr hb)
  obtain ⟨⟨_, j, hj⟩, _⟩ := hb
  have hyb' : dist y (P.ι b.1) < b.2 := hyb
  refine ⟨j, hj ?_, hj ?_⟩
  · rw [Metric.mem_ball]
    have : (0 : ℝ) ≤ b.2 := le_trans dist_nonneg hyb'.le
    linarith
  · rw [Metric.mem_ball]
    have := dist_triangle z y (P.ι b.1)
    rw [dist_comm] at hyz
    linarith

omit [CompactSpace X] in
open Classical in
/-- Step 3 of Theorem 1(b): if `μ(V) > 1 - θ` for an `A`-c.e. open `V`, the orbit of a random
point leaves `V` at most `θ n` times before time `n`, for all large `n`. -/
private theorem eventually_card_bad_le (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (herg : Ergodic T μ) {V : Set X} (hV : IsCeOpenIn P A V) {x : X}
    (hx : x ∈ randomPoints P A μ) {θ : ℝ} (hθ : ENNReal.ofReal (1 - θ) < μ V) :
    ∀ᶠ n : ℕ in atTop, (((List.range n).countP fun k ↦ decide (T^[k] x ∉ V) : ℕ) : ℝ) ≤
      θ * n := by
  classical
  have h := measure_le_liminf_visitFrequency P T A μ hA herg hV hx
  have h2 := eventually_lt_of_lt_liminf (hθ.trans_le h)
  filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
  have hset : {k | k < n ∧ T^[k] x ∈ V} =
      ↑((Finset.range n).filter fun k ↦ T^[k] x ∈ V) := by
    ext k
    simp
  rw [hset, Set.ncard_coe_finset, natCast_div_eq_ofReal _ hn1] at hn
  have hcount : (List.range n).countP (fun k ↦ decide (T^[k] x ∉ V)) +
      ((Finset.range n).filter fun k ↦ T^[k] x ∈ V).card = n := by
    have h1 : ((Finset.range n).filter fun k ↦ T^[k] x ∈ V).card =
        (List.range n).countP (fun k ↦ decide (T^[k] x ∈ V)) := by
      rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
        Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter]
    rw [h1, add_comm]
    have := List.length_eq_countP_add_countP (fun k ↦ decide (T^[k] x ∈ V)) (l := List.range n)
    simp only [List.length_range, decide_not, decide_eq_true_eq] at this ⊢
    omega
  have hn' : 1 - θ < (((Finset.range n).filter fun k ↦ T^[k] x ∈ V).card : ℝ) / n :=
    ((ENNReal.ofReal_lt_ofReal_iff'.mp hn).1)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [lt_div_iff₀ hnr] at hn'
  have hc : (((List.range n).countP fun k ↦ decide (T^[k] x ∉ V) : ℕ) : ℝ) +
      (((Finset.range n).filter fun k ↦ T^[k] x ∈ V).card : ℝ) = n := by
    exact_mod_cast hcount
  nlinarith

/-- Theorem 1(b), at fixed scales: for every `H < h_μ(T)` there is `ε₀ > 0` such that
`liminf_n K_n^A(x, T, ε) / n ≥ H` for all `0 < ε ≤ ε₀`, at every `μ`-random point.
Blueprint node `erg:theorem-one`. -/
theorem exists_le_orbitComplexityAt_fst (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (herg : Ergodic T μ) {x : X}
    (hx : x ∈ randomPoints P A μ) {H : ℝ≥0∞} (hH : H < Ergodic.ksEntropy μ T) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → H ≤ (orbitComplexityAt P T A x ε).1 := by
  classical
  have hmp : MeasurePreserving T μ μ := herg.toMeasurePreserving
  -- Step 1: a computable partition with entropy rate `> H₁ > H`
  obtain ⟨H₁, hHH₁, hH₁⟩ := exists_between hH
  obtain ⟨δ, hδ, hδH⟩ := Ergodic.lt_entropyRate_of_diam_lt hmp hH₁
  have : Nonempty X := ⟨x⟩
  obtain ⟨p, U, Q, hp, hU, hQ, hUQ, hdiam⟩ := exists_computablePartition P A μ hA.1 hA.2.2 hδ
  have : NeZero p := ⟨hp.ne'⟩
  have hHQ : H₁ < Ergodic.entropyRate μ T Q := hδH p Q hQ hdiam
  have hHtop : H ≠ ⊤ := ne_top_of_lt hH
  have hH₁top : H₁ ≠ ⊤ := ne_top_of_lt hHQ
  set h : ℝ := H.toReal with hh
  set η : ℝ := H₁.toReal - h with hηdef
  have hη : 0 < η := by
    have := (ENNReal.toReal_lt_toReal hHtop hH₁top).mpr hHH₁
    rw [hηdef]
    linarith
  -- Step 5: the symbolic lower bound for the itinerary `ω`
  set ω : ℕ → Fin p := symbolicCode T U x with hω
  have : IsProbabilityMeasure (codedMeasure μ T U) :=
    isProbabilityMeasure_codedMeasure hT.measurable hU
  have hlim : H₁ < liminf (fun n : ℕ ↦ (wordComplexity A ω n : ℝ≥0∞) / n) atTop := by
    calc H₁ < Ergodic.entropyRate μ T Q := hHQ
      _ = shiftEntropy (codedMeasure μ T U) := (shiftEntropy_codedMeasure hmp hU hQ hUQ).symm
      _ ≤ _ := shiftEntropy_le_liminf_wordComplexity A _ (ergodic_codedMeasure herg hU)
          (isComputableWordMeasureIn_codedMeasure hA hmp hU)
          (symbolicCode_mem_wordRandomPoints hA hmp hU hx)
  have hev1 := eventually_lt_of_lt_liminf hlim
  -- Step 4: the decoder and the coding of the side information
  obtain ⟨cd, hcd⟩ := orbitLower_decoder P T A hA.1 hA.2.1 hU.1 hU.2.1
  obtain ⟨B, d, hB, hBd⟩ := orbitLower_optionList_bound A (β := Fin p) (η := η / 4)
    (by positivity)
  set θ : ℝ := min 1 (η / (4 * (B + 1))) with hθdef
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθB : B * θ ≤ η / 4 := by
    have h1 : θ ≤ η / (4 * (B + 1)) := min_le_right _ _
    have h2 : B * θ ≤ (B + 1) * θ := by nlinarith
    have h3 : (B + 1) * θ ≤ (B + 1) * (η / (4 * (B + 1))) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : (B + 1) * (η / (4 * (B + 1))) = η / 4 := by
      field_simp
    linarith
  -- Step 2: the region `V` where close points share an atom
  have hUo : ∀ j, IsOpen (U j) := by
    obtain ⟨E, -, hUeq⟩ := hU.1
    intro j
    rw [hUeq j]
    exact isOpen_biUnion fun b _ ↦ Metric.isOpen_ball
  obtain ⟨L, δ₀, hδ₀, hμV, hshadow⟩ := exists_ballUnion_shadow P μ hUo hU.2.2 hθ0
  set V := ballUnion P L with hVdef
  have hVce : IsCeOpenIn P A V := by
    obtain ⟨E, hE, hEq⟩ := ballUnion_ceOpen (P := P) (B := A)
    exact ⟨fun b ↦ E (L, b), hE.comp ((Computable.const L).pair Computable.id).computableIn,
      hEq L⟩
  -- Step 3: the orbit is mostly in `V`
  have hev2 := eventually_card_bad_le P T A μ hA herg hVce hx hμV
  have hxD := randomPoints_subset_codingDomain hA hmp hU hx
  refine ⟨δ₀, hδ₀, fun ε hε hεδ ↦ ?_⟩
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hev1, hev2, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈2 * (|d| + cd) / η⌉₊] with n h1 h2 hn1 hn2
  rw [entropiesAndOrbitComplexities_rate P T hT A x n hn1 ε hε]
  obtain ⟨i, hi, hKi⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn1 ε hε
  have hK : orbitComplexityNat P T A x n ε = oracleNatComplexity A i := by
    simp [orbitComplexityNat, hKi]
  rw [hK]
  -- the side information
  set v : List (Option (Fin p)) :=
    (List.range n).map fun k ↦ if T^[k] x ∈ V then none else some (ω k) with hv
  have hcompat : OrbitLowerCompatible P T U i v (wordPrefix ω n) := by
    refine ⟨by simp [hv, wordPrefix], fun k hk ↦ ?_⟩
    have hkn : k < n := by simpa [wordPrefix] using hk
    have hwk : (wordPrefix ω n).get ⟨k, hk⟩ = ω k := by simp [wordPrefix]
    have hvk : v.getD k none = if T^[k] x ∈ V then none else some (ω k) := by simp [hv, hkn]
    rw [hwk, hvk]
    by_cases hkV : T^[k] x ∈ V
    · right
      refine ⟨by simp [hkV], ?_⟩
      have hdist : dist (T^[k] x) (T^[k] (P.ι i)) < δ₀ :=
        lt_of_lt_of_le (Dynamics.mem_dynEntourage.mp hi k hkn) hεδ
      obtain ⟨j, hxj, hij⟩ := hshadow _ hkV _ hdist
      have hxω := iterate_mem_symbolicCode hU.2.1 hxD k
      have hj : j = ω k := by
        by_contra hne
        exact Set.disjoint_left.mp (hU.2.1 hne) hxj hxω
      rw [← hj]
      exact hij
    · left
      simp [hkV]
  have hcountv : v.countP Option.isSome =
      (List.range n).countP fun k ↦ decide (T^[k] x ∉ V) := by
    rw [hv, List.countP_map]
    congr 1
    funext k
    by_cases hk : T^[k] x ∈ V <;> simp [hk]
  have hvlen : v.length = n := by simp [hv]
  have hdec := hcd i v _ hcompat
  have hcode := hBd v
  rw [hvlen, hcountv] at hcode
  have hW : (wordComplexity A ω n : ℝ) ≤
      oracleNatComplexity A i + η / 4 * n + B * θ * n + d + cd := by
    have : (wordComplexity A ω n : ℝ) ≤
        oracleNatComplexity A i + oracleComplexity A (natBits (Encodable.encode v)) + cd := by
      exact_mod_cast hdec
    have hb : B * (((List.range n).countP fun k ↦ decide (T^[k] x ∉ V) : ℕ) : ℝ) ≤
        B * (θ * n) := mul_le_mul_of_nonneg_left h2 hB
    nlinarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlow : (n : ℝ) * (h + η) < wordComplexity A ω n := by
    rw [natCast_div_eq_ofReal _ hn1, ← ENNReal.ofReal_toReal hH₁top,
      ENNReal.ofReal_lt_ofReal_iff'] at h1
    have := h1.1
    rw [lt_div_iff₀ hnr] at this
    have hH₁r : H₁.toReal = h + η := by rw [hηdef]; ring
    rw [hH₁r] at this
    linarith
  have hn2' : 2 * (|d| + cd) / η ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
  rw [div_le_iff₀ hη] at hn2'
  have hdabs : d ≤ |d| := le_abs_self d
  have hKi_ge : h * n ≤ oracleNatComplexity A i := by
    nlinarith
  rw [natCast_div_eq_ofReal _ hn1, ← ENNReal.ofReal_toReal hHtop]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hnr]
  exact hKi_ge

/-- Theorem 1(b): `h_μ(T) ≤ K̲^A(x, T)` at every `μ`-random point.
Blueprint node `erg:theorem-one`. -/
theorem ksEntropy_le_lowerOrbitComplexity (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (herg : Ergodic T μ) {x : X}
    (hx : x ∈ randomPoints P A μ) :
    Ergodic.ksEntropy μ T ≤ (orbitComplexities P T A x).1 := by
  refine le_of_forall_lt_imp_le_of_dense fun H hH ↦ ?_
  obtain ⟨ε₀, hε₀, hle⟩ := exists_le_orbitComplexityAt_fst P T hT A μ hA herg hx hH
  exact (hle ε₀ hε₀ le_rfl).trans (orbitComplexityAt_le_orbitComplexities P T A x hε₀).1

end Kolmogorov.PointToSet
