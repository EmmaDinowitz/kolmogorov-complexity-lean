/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.SymbolicCoding
import KolmogorovMathlib.Ergodic.MeanErgodic

/-!
# Random points visit effectively open sets with the right frequency

Input (I2) of the note *Orbit complexity of Martin-Löf random points equals entropy* (random
points are typical, Galatolo–Hoyrup–Rojas 2010, Theorem 3.2.1) is used there in one form only,
which is proved here:

* `measure_le_liminf_visitFrequency` (I2′): if `T` is `A`-represented and ergodic for the
  `A`-computable probability measure `μ`, `U` is `A`-effectively open and `x` is `μ`-random
  relative to `A`, then `liminf_n (1/n) #{k < n | T^k x ∈ U} ≥ μ(U)`.

  Proof (effective Birkhoff theorem without integrals or computable functions,
  `typical_visitCount_lower_of_random`). Fix rationals `q < μ(U)` and `η > 0`. Choose finitely
  many basic balls with shrunk rational radii whose closures lie in `U` and whose open union
  `W°` has `μ(W°) > q` (`typical_exists_ballList`); let `W̄ ⊆ U` be the union of the closed
  balls. Write `#_N(V, y) = #{k < N | T^k y ∈ V}` (`typicalVisitCount`). The sets
  `G_N = {#_N(W°, ·) > (q - η/16) N}` and `B_N = {#_N(W̄, ·) < (q - η/8) N}` are `A`-c.e. open
  uniformly in `N` (`isCeOpenFamilyIn_typicalVisitCount_gt`, from the c.e. openness of the preimages
  under iterates, `isCeOpenFamilyIn_iterate_preimage_typical`; `W̄ᶜ` is c.e. open) and
  disjoint, so `μ(B_N) ≤ 1 - μ(G_N)`. By the `L¹` mean ergodic theorem
  (`tendsto_integral_abs_birkhoffAverage_sub`) and Markov's inequality, `μ(G_N) → 1`
  (`typical_exists_measure_visitCount_gt`); since `μ(G_N)` is lower semicomputable (M1), one can
  search for `N(m)` with `μ(G_{N(m)}) > 1 - δ_m`, `δ_m = η 2^{-m-1}`. The sets
  `E_m = {y | ∃ n, #_n(B_{N(m)}, y) > n η/2}` are uniformly `A`-c.e. open and, by the maximal
  inequality (`measure_maximal_birkhoffAverage_le`, `typical_measure_visitCount_maximal`),
  `μ(E_m) ≤ 2^{-m}`: a test. A random `x` avoids some `E_m`, and then a double count
  (`typical_visitCount_lower`) gives `#_n(U, x) ≥ #_n(W̄, x) ≥ (1 - η/2)(q - η/8) n - N(m)`.
* `isGenericPoint_symbolicCode`: the itinerary `φ(x)` of a random point is generic for the coded
  measure `ν`. Proof: apply (I2′) to the cells `O_w = ⋂_{k<n} T^{-k} U_{w_k}`, which are
  `A`-c.e. open, pairwise disjoint and of total measure `1`, with `ν[w] = μ(O_w)`
  (`codedMeasure_wordCylinder`). Every visit of the orbit of `x` to `O_w` is an occurrence of
  `w` in `φ(x)`, and the frequencies of the words of a fixed length sum to `1`, so the lower
  bounds `≥ ν[w]` on the frequencies force them to converge to `ν[w]`.

Blueprint node `erg:typical`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

section counting

variable {X : Type*}

open Classical in
/-- The number of visits `#{k < n | T^k y ∈ V}` of the orbit of `y` to `V` before time `n`. -/
noncomputable def typicalVisitCount (T : X → X) (V : Set X) (n : ℕ) (y : X) : ℕ :=
  ((Finset.range n).filter fun k ↦ T^[k] y ∈ V).card

open Classical in
/-- The visit count as the length of a filtered list. -/
theorem typicalVisitCount_eq_length (T : X → X) (V : Set X) (n : ℕ) (y : X) :
    typicalVisitCount T V n y =
      ((List.range n).filter fun k ↦ decide (T^[k] y ∈ V)).length :=
  rfl

open Classical in
/-- The visit count as a sum of indicators. -/
theorem typicalVisitCount_eq_sum (T : X → X) (V : Set X) (n : ℕ) (y : X) :
    typicalVisitCount T V n y = ∑ k ∈ Finset.range n, if T^[k] y ∈ V then 1 else 0 :=
  Finset.card_filter _ _

/-- The visit count is monotone in the visited set. -/
theorem typicalVisitCount_mono (T : X → X) {V V' : Set X} (h : V ⊆ V') (n : ℕ) (y : X) :
    typicalVisitCount T V n y ≤ typicalVisitCount T V' n y := by
  classical
  exact Finset.card_le_card (Finset.monotone_filter_right _ fun k _ hk ↦ h hk)

/-- Visits to a set and to its complement add up to the elapsed time. -/
theorem typicalVisitCount_add_compl (T : X → X) (V : Set X) (n : ℕ) (y : X) :
    typicalVisitCount T V n y + typicalVisitCount T Vᶜ n y = n := by
  classical
  unfold typicalVisitCount
  convert Finset.card_filter_add_card_filter_not (s := Finset.range n)
    (fun k ↦ T^[k] y ∈ V) using 1
  · simp
  · simp

/-- The visit count as a Birkhoff sum of an indicator. -/
theorem birkhoffSum_indicator_eq_typicalVisitCount (T : X → X) (V : Set X) (n : ℕ) (y : X) :
    birkhoffSum T (V.indicator (1 : X → ℝ)) n y = typicalVisitCount T V n y := by
  classical
  rw [typicalVisitCount, Finset.natCast_card_filter, birkhoffSum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [indicator_apply, Pi.one_apply]

/-- The visit count as the cardinality of the set of visit times. -/
theorem ncard_eq_typicalVisitCount (T : X → X) (V : Set X) (n : ℕ) (y : X) :
    ({k | k < n ∧ T^[k] y ∈ V} : Set ℕ).ncard = typicalVisitCount T V n y := by
  classical
  rw [typicalVisitCount, ← Set.ncard_coe_finset]
  congr 1
  ext k
  simp

open Classical in
/-- A shifted window of visits is controlled by the visits before time `n`:
`∑_{k<n} 1_W(T^{j+k} x) ≤ #{i < n | T^i x ∈ W} + j`. -/
theorem typical_sum_shift_le (T : X → X) (W : Set X) (x : X) (n j : ℕ) :
    ∑ k ∈ Finset.range n, (if T^[j + k] x ∈ W then 1 else 0) ≤
      typicalVisitCount T W n x + j := by
  rw [typicalVisitCount_eq_sum]
  have h1 := Finset.sum_range_add (fun i ↦ if T^[i] x ∈ W then 1 else 0) j n
  have h2 := Finset.sum_range_add (fun i ↦ if T^[i] x ∈ W then 1 else 0) n j
  have h3 : ∑ k ∈ Finset.range j, (if T^[n + k] x ∈ W then 1 else 0) ≤ j := by
    calc ∑ k ∈ Finset.range j, (if T^[n + k] x ∈ W then 1 else 0)
        ≤ ∑ _k ∈ Finset.range j, 1 := Finset.sum_le_sum fun k _ ↦ by split_ifs <;> simp
      _ = j := by simp
  rw [add_comm j n] at h1
  omega

/-- Deterministic core of the effective Birkhoff theorem: if every point outside `B` spends at
least the fraction `a` of a window of length `N` in `W`, and the orbit of `x` spends at most the
fraction `θ` of every initial segment in `B`, then `#{k < n | T^k x ∈ W} ≥ (1 - θ) a n - N`. -/
theorem typical_visitCount_lower (T : X → X) {W B : Set X} {N : ℕ} (hN : 1 ≤ N) {a θ : ℝ}
    (ha : 0 ≤ a) (hB : ∀ y, y ∉ B → a * N ≤ typicalVisitCount T W N y) {x : X}
    (hx : ∀ n : ℕ, (typicalVisitCount T B n x : ℝ) ≤ θ * n) (n : ℕ) :
    (1 - θ) * a * n - N ≤ typicalVisitCount T W n x := by
  classical
  -- upper bound of the double sum
  have hup : ∑ k ∈ Finset.range n, typicalVisitCount T W N (T^[k] x) ≤
      N * (typicalVisitCount T W n x + N) := by
    have hrw : ∀ k, typicalVisitCount T W N (T^[k] x) =
        ∑ j ∈ Finset.range N, if T^[j + k] x ∈ W then 1 else 0 := by
      intro k
      rw [typicalVisitCount_eq_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Function.iterate_add_apply]
    simp_rw [hrw]
    rw [Finset.sum_comm]
    calc ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range n, (if T^[j + k] x ∈ W then 1 else 0)
        ≤ ∑ _j ∈ Finset.range N, (typicalVisitCount T W n x + N) := by
          refine Finset.sum_le_sum fun j hj ↦ ?_
          have := typical_sum_shift_le T W x n j
          have hj' := Finset.mem_range.mp hj
          omega
      _ = N * (typicalVisitCount T W n x + N) := by simp
  -- lower bound of the double sum
  have hlow : a * N * n - a * N * typicalVisitCount T B n x ≤
      ∑ k ∈ Finset.range n, (typicalVisitCount T W N (T^[k] x) : ℝ) := by
    have hB' : (typicalVisitCount T B n x : ℝ) =
        ∑ k ∈ Finset.range n, if T^[k] x ∈ B then (1 : ℝ) else 0 := by
      rw [typicalVisitCount, Finset.natCast_card_filter]
    rw [hB', Finset.mul_sum]
    calc a * N * n - ∑ k ∈ Finset.range n, a * N * (if T^[k] x ∈ B then (1 : ℝ) else 0)
        = ∑ k ∈ Finset.range n, (a * N - a * N * (if T^[k] x ∈ B then (1 : ℝ) else 0)) := by
          rw [Finset.sum_sub_distrib]
          simp [mul_comm]
      _ ≤ ∑ k ∈ Finset.range n, (typicalVisitCount T W N (T^[k] x) : ℝ) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          by_cases hk : T^[k] x ∈ B
          · simp [hk]
          · simpa [hk] using hB _ hk
  have hupR : ∑ k ∈ Finset.range n, (typicalVisitCount T W N (T^[k] x) : ℝ) ≤
      N * (typicalVisitCount T W n x + N) := by exact_mod_cast hup
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have haN : 0 ≤ a * N := mul_nonneg ha hNpos.le
  have hxn := mul_le_mul_of_nonneg_left (hx n) haN
  have key : (N : ℝ) * ((1 - θ) * a * n) ≤ N * (typicalVisitCount T W n x + N) := by
    nlinarith
  have := le_of_mul_le_mul_left key hNpos
  linarith

/-- Birkhoff averages of an indicator are visit frequencies. -/
theorem birkhoffAverage_indicator_eq_typical (T : X → X) (V : Set X) (n : ℕ) (y : X) :
    birkhoffAverage ℝ T (V.indicator (1 : X → ℝ)) n y = typicalVisitCount T V n y / n := by
  rw [birkhoffAverage, birkhoffSum_indicator_eq_typicalVisitCount, smul_eq_mul, inv_mul_eq_div]

end counting

section measure

variable {X : Type*} [MeasurableSpace X]

/-- Birkhoff sums of a measurable function along a measurable map are measurable. -/
theorem measurable_birkhoffSum_typical {T : X → X} (hT : Measurable T) {g : X → ℝ}
    (hg : Measurable g) (n : ℕ) : Measurable (birkhoffSum T g n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ fun k _ ↦ hg.comp (hT.iterate k)

/-- By the mean ergodic theorem, for `c < μ(W)` the set where the visit frequency to `W` up to
time `N` exceeds `c` has measure arbitrarily close to `1` for suitable `N ≥ 1`. -/
theorem typical_exists_measure_visitCount_gt {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : Ergodic T μ) {W : Set X} (hW : MeasurableSet W) {c : ℝ}
    (hc : c < μ.real W) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 1 ≤ N ∧ 1 - δ < μ.real {y | c * N < typicalVisitCount T W N y} := by
  set g : X → ℝ := W.indicator 1 with hg_def
  have hg : Measurable g := measurable_one.indicator hW
  have hC : ∀ y, |g y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ W <;> simp [hg_def, hy]
  have hTm : Measurable T := hT.toMeasurePreserving.measurable
  have hlim := Kolmogorov.Ergodic.tendsto_integral_abs_birkhoffAverage_sub hT hg hC
  rw [integral_indicator_one hW] at hlim
  set gap := μ.real W - c with hgap
  have hgap0 : 0 < gap := by linarith
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hlim).2 _ (mul_pos hgap0 hδ)).and
    (eventually_ge_atTop 1) |>.exists
  refine ⟨N, hN.2, ?_⟩
  set f : X → ℝ := fun y ↦ |birkhoffAverage ℝ T g N y - μ.real W| with hf_def
  have hfm : Measurable f := by
    have hav : Measurable (birkhoffAverage ℝ T g N) :=
      (measurable_birkhoffSum_typical hTm hg N).const_smul ((N : ℝ)⁻¹)
    exact continuous_abs.measurable.comp (hav.sub_const _)
  have hfint : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable 2 (ae_of_all _ fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have h1 : 0 ≤ birkhoffAverage ℝ T g N y := by
      rw [hg_def, birkhoffAverage_indicator_eq_typical]
      positivity
    have h2 : birkhoffAverage ℝ T g N y ≤ 1 := by
      rw [hg_def, birkhoffAverage_indicator_eq_typical]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.2
      rw [div_le_one hN0]
      have := typicalVisitCount_add_compl T W N y
      have : typicalVisitCount T W N y ≤ N := by omega
      exact_mod_cast this
    have h3 : μ.real W ≤ 1 := measureReal_le_one
    have h4 : 0 ≤ μ.real W := measureReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun y ↦ abs_nonneg _) hfint gap
  have hsmall : μ.real {y | gap ≤ f y} < δ := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_left hcon hgap0.le
    linarith [hN.1]
  have hsub : {y | c * N < typicalVisitCount T W N y}ᶜ ⊆ {y | gap ≤ f y} := by
    intro y hy
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hy
    simp only [mem_ofPred_eq, hf_def]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.2
    have hav : birkhoffAverage ℝ T g N y ≤ c := by
      rw [hg_def, birkhoffAverage_indicator_eq_typical, div_le_iff₀ hN0]
      linarith
    rw [abs_sub_comm, hgap]
    exact (by linarith : μ.real W - c ≤ μ.real W - birkhoffAverage ℝ T g N y).trans
      (le_abs_self _)
  have hunion : 1 ≤ μ.real {y | c * N < typicalVisitCount T W N y} +
      μ.real {y | c * N < typicalVisitCount T W N y}ᶜ := by
    have := measureReal_union_le (μ := μ) {y | c * N < typicalVisitCount T W N y}
      {y | c * N < typicalVisitCount T W N y}ᶜ
    rwa [union_compl_self, probReal_univ] at this
  linarith [measureReal_mono (μ := μ) hsub]

/-- The maximal inequality for an indicator: the set of points spending more than the fraction
`θ` of some initial segment of their orbit in `B` has measure at most `μ(B) / θ`. -/
theorem typical_measure_visitCount_maximal {μ : Measure X} [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) {B : Set X} (hB : MeasurableSet B) {θ : ℝ}
    (hθ : 0 < θ) :
    θ * μ.real {y | ∃ n : ℕ, θ * n < typicalVisitCount T B n y} ≤ μ.real B := by
  have hg : Integrable (B.indicator (1 : X → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hB
  have hmax := Kolmogorov.Ergodic.measure_maximal_birkhoffAverage_le hT hg hθ
  have habs : ∫ y, |B.indicator (1 : X → ℝ) y| ∂μ = μ.real B := by
    rw [← integral_indicator_one hB]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    by_cases hy : y ∈ B <;> simp [hy]
  rw [habs] at hmax
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono fun y hy ↦ ?_) hθ.le) hmax
  obtain ⟨n, hn⟩ := hy
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [typicalVisitCount] at hn
    · exact h
  refine ⟨n, hn1, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [birkhoffAverage_indicator_eq_typical, lt_div_iff₀ hn0]
  linarith

end measure

section effective

variable {X : Type*} [MetricSpace X]

/-- Preimages of a c.e. open family under the iterates of an `A`-represented map are c.e. open,
uniformly in the index and in the number of iterations. -/
theorem isCeOpenFamilyIn_iterate_preimage_typical {P : Presentation X} {T : X → X} {A : Set ℕ}
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) {κ : Type*}
    [Primcodable κ] {V : κ → Set X} (hV : IsCeOpenFamilyIn P A V) :
    IsCeOpenFamilyIn P A fun d : κ × ℕ ↦ T^[d.2] ⁻¹' V d.1 := by
  obtain ⟨E, hE, hVE⟩ := hV
  have hlt := birkhoff_computableIn_lt A _ hP
  obtain ⟨R', hR're, hR's, hR'small⟩ := exists_bowenChainRep P T A hP hTA
  -- step condition for the parameter `(i, k₀)` at time `k`: free before `k₀`, certified inside a
  -- listed ball of `V i` at time `k₀`
  let C : ((κ × ℕ) × ℕ) × (ℕ × ℚ) → Prop := fun w ↦
    0 < w.2.2 ∧ (w.1.2 < w.1.1.2 ∨ ∃ b : ℕ × ℚ, E (w.1.1.1, b) ∧
      dist (P.ι w.2.1) (P.ι b.1) < ((b.2 - w.2.2 : ℚ) : ℝ))
  have hCre : IsREIn A C := by
    have h1 : IsREIn A fun v : (((κ × ℕ) × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦ E (v.1.1.1.1, v.2) :=
      hE.comp ((Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
        Computable.fst))).pair Computable.snd).computableIn
    have h2 : IsREIn A fun v : (((κ × ℕ) × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        dist (P.ι v.1.2.1) (P.ι v.2.1) < ((v.2.2 - v.1.2.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp Computable.snd)).pair
        (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
    exact (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp Computable.snd))).and
      ((isREIn_of_computable_decide (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).decide.to_comp).or (h1.and h2).exists)
  have hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c') := by
    rintro a k c z ⟨_, hc | ⟨b, hb, hcb⟩⟩ hz
    · exact ⟨1, one_pos, fun c' hc'0 _ _ ↦ ⟨hc'0, Or.inl hc⟩⟩
    · have hz' : dist z (P.ι c.1) < c.2 := hz
      push_cast at hcb
      have hzb : dist z (P.ι b.1) < b.2 := by
        linarith [dist_triangle z (P.ι c.1) (P.ι b.1)]
      refine ⟨(b.2 - dist z (P.ι b.1)) / 2, by linarith, fun c' hc'0 hc'δ hzc' ↦
        ⟨hc'0, Or.inr ⟨b, hb, ?_⟩⟩⟩
      have hzc'' : dist z (P.ι c'.1) < c'.2 := hzc'
      push_cast
      linarith [dist_triangle (P.ι c'.1) z (P.ι b.1), dist_comm z (P.ι c'.1)]
  have H := isCeOpenFamilyIn_bowenChainSet P T A hR're hR's hR'small hCre hCloc
  have heq : ∀ (i : κ) (k₀ : ℕ), bowenChainSet P T C (i, k₀) (k₀ + 1) = T^[k₀] ⁻¹' V i := by
    intro i k₀
    ext y
    constructor
    · intro hy
      obtain ⟨c, ⟨_, hc⟩, hyc⟩ := hy k₀ (Nat.lt_succ_self k₀)
      obtain ⟨b, hb, hcb⟩ := hc.resolve_left (lt_irrefl k₀)
      have hyc' : dist (T^[k₀] y) (P.ι c.1) < c.2 := hyc
      push_cast at hcb
      change T^[k₀] y ∈ V i
      rw [hVE i]
      refine mem_iUnion₂.mpr ⟨b, hb, ?_⟩
      change dist (T^[k₀] y) (P.ι b.1) < b.2
      linarith [dist_triangle (T^[k₀] y) (P.ι c.1) (P.ι b.1)]
    · intro hy k hk
      rcases Nat.lt_or_ge k k₀ with hkk | hkk
      · obtain ⟨c, hc0, _, hyc⟩ := bowenChain_exists_small_ball P (T^[k] y) one_pos
        exact ⟨c, ⟨hc0, Or.inl hkk⟩, hyc⟩
      · obtain rfl : k = k₀ := by omega
        have hy' : T^[k] y ∈ V i := hy
        rw [hVE i] at hy'
        obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy'
        have hyb' : dist (T^[k] y) (P.ι b.1) < b.2 := hyb
        obtain ⟨c, hc0, hcδ, hyc⟩ := bowenChain_exists_small_ball P (T^[k] y)
          (δ := (b.2 - dist (T^[k] y) (P.ι b.1)) / 2) (by linarith)
        have hyc' : dist (T^[k] y) (P.ι c.1) < c.2 := hyc
        refine ⟨c, ⟨hc0, Or.inr ⟨b, hb, ?_⟩⟩, hyc⟩
        push_cast
        linarith [dist_triangle (P.ι c.1) (T^[k] y) (P.ι b.1), dist_comm (T^[k] y) (P.ι c.1)]
  have hg : Computable fun d : κ × ℕ ↦ (d, d.2 + 1) :=
    Computable.id.pair (Primrec.succ.comp Primrec.snd).to_comp
  have h := H.comp hg
  have hfun : (fun d : κ × ℕ ↦ T^[d.2] ⁻¹' V d.1) =
      fun d ↦ bowenChainSet P T C (d, d.2 + 1).1 (d, d.2 + 1).2 :=
    funext fun d ↦ (heq d.1 d.2).symm
  rw [hfun]
  exact h

/-- Membership of a natural number in a list of natural numbers is primitive recursive. -/
theorem primrecRel_mem_typical : PrimrecRel fun (k : ℕ) (L : List ℕ) ↦ k ∈ L := by
  have h : PrimrecPred fun p : ℕ × List ℕ ↦ p.2.idxOf p.1 < p.2.length :=
    Primrec.nat_lt.comp ((Primrec.list_idxOf (α := ℕ)).comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)
  refine PrimrecPred.of_eq h fun p ↦ ?_
  exact List.idxOf_lt_length_iff

/-- The sublist of `[0, n)` of the members of a list `L` is primitive recursive in `(n, L)`. -/
theorem primrec_filter_typical :
    Primrec fun nL : ℕ × List ℕ ↦ (List.range nL.1).filter fun k ↦ decide (k ∈ nL.2) :=
  primrecRel_mem_typical.listFilter.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd

/-- The sets `{y | c < #{k < n | T^k y ∈ V_i}}` are c.e. open, uniformly in `(i, n, c)`. -/
theorem isCeOpenFamilyIn_typicalVisitCount_gt {P : Presentation X} {T : X → X} {A : Set ℕ}
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) {κ : Type*}
    [Primcodable κ] {V : κ → Set X} (hV : IsCeOpenFamilyIn P A V) :
    IsCeOpenFamilyIn P A fun d : κ × ℕ × ℚ ↦
      {y | (d.2.2 : ℝ) < typicalVisitCount T (V d.1) d.2.1 y} := by
  classical
  have H := (isCeOpenFamilyIn_iterate_preimage_typical hP hTA hV).biInter_list hP
  let F : ℕ × List ℕ → List ℕ := fun nL ↦ (List.range nL.1).filter fun k ↦ decide (k ∈ nL.2)
  have hF : Computable F := primrec_filter_typical.to_comp
  have hg : Computable fun w : (κ × ℕ × ℚ) × List ℕ ↦ (w.1.1, F (w.1.2.1, w.2)) :=
    (Computable.fst.comp Computable.fst).pair (hF.comp ((Computable.fst.comp
      (Computable.snd.comp Computable.fst)).pair Computable.snd))
  have hp : Computable fun w : (κ × ℕ × ℚ) × List ℕ ↦
      decide (w.1.2.2 < ((F (w.1.2.1, w.2)).length : ℚ)) :=
    computable₂_ratLt.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
      (computable_nat_to_rat.comp ((Primrec.list_length.to_comp).comp (hF.comp
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))))
  have H' := ((H.comp hg).ite hp).iUnion
  convert H' using 1
  funext d
  obtain ⟨i, n, c⟩ := d
  ext y
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hy
    refine ⟨(List.range n).filter fun k ↦ decide (T^[k] y ∈ V i), ?_⟩
    have hFL : F (n, (List.range n).filter fun k ↦ decide (T^[k] y ∈ V i)) =
        (List.range n).filter fun k ↦ decide (T^[k] y ∈ V i) := by
      refine List.filter_congr fun k hk ↦ ?_
      have hk' : k < n := List.mem_range.mp hk
      simp [hk']
    simp only [hFL]
    rw [typicalVisitCount_eq_length] at hy
    have hy' : c < (((List.range n).filter fun k ↦ decide (T^[k] y ∈ V i)).length : ℚ) := by
      exact_mod_cast hy
    simp only [hy', ↓reduceIte, mem_iInter]
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  · rintro ⟨L, hL⟩
    by_cases hc : c < ((F (n, L)).length : ℚ)
    · simp only [hc, ↓reduceIte, mem_iInter] at hL
      rw [typicalVisitCount_eq_length]
      have hle : (F (n, L)).length ≤
          ((List.range n).filter fun k ↦ decide (T^[k] y ∈ V i)).length := by
        rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
        refine List.countP_mono_left fun k hk hkL ↦ ?_
        exact decide_eq_true (hL k (List.mem_filter.mpr ⟨hk, hkL⟩))
      have hc' : (c : ℝ) < (F (n, L)).length := by exact_mod_cast hc
      exact hc'.trans_le (by exact_mod_cast hle)
    · simp only [hc, ↓reduceIte] at hL
      exact hL.elim

/-- Sets that are uniformly c.e. open are open. -/
theorem isOpen_of_isCeOpenFamilyIn_typical {P : Presentation X} {A : Set ℕ} {ι : Type*}
    [Primcodable ι] {V : ι → Set X} (hV : IsCeOpenFamilyIn P A V) (i : ι) : IsOpen (V i) :=
  isOpen_of_isCeOpenFamilyIn hV i

end effective

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Inner approximation of an effectively open set by finitely many shrunk basic balls: there
is a finite list of basic balls whose closures lie in `U` and whose union has measure `> r`. -/
theorem typical_exists_ballList (P : Presentation X) {A : Set ℕ} {μ : Measure X} {U : Set X}
    (hU : IsCeOpenIn P A U) {r : ℝ≥0∞} (hr : r < μ U) :
    ∃ L : List (ℕ × ℚ), (∀ b ∈ L, ∀ y, dist (P.ι b.1) y ≤ b.2 → y ∈ U) ∧
      r < μ (ballUnion P L) := by
  classical
  obtain ⟨E, -, rfl⟩ := hU
  let S : ℕ → Set (ℕ × ℚ) := fun n ↦ {b | E b ∧ Encodable.encode b ≤ n}
  have hS : ∀ n, (S n).Finite := fun n ↦
    ((Set.finite_le_nat n).preimage Encodable.encode_injective.injOn).subset fun b hb ↦ hb.2
  let W : ℕ → Set X := fun n ↦
    ⋃ b ∈ S n, Metric.ball (P.ι b.1) ((b.2 : ℝ) - 1 / ((n : ℝ) + 1))
  have hmono : Monotone W := by
    intro n m hnm y hy
    simp only [W, mem_iUnion] at hy ⊢
    obtain ⟨b, ⟨hEb, hbn⟩, hy⟩ := hy
    refine ⟨b, ⟨hEb, hbn.trans hnm⟩, Metric.ball_subset_ball ?_ hy⟩
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hunion : (⋃ n, W n) = ⋃ b ∈ {b | E b}, basicBall P b := by
    ext y
    simp only [W, mem_iUnion]
    constructor
    · rintro ⟨n, b, ⟨hEb, -⟩, hy⟩
      refine ⟨b, hEb, Metric.ball_subset_ball ?_ hy⟩
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · rintro ⟨b, hEb, hy⟩
      have hy' : dist y (P.ι b.1) < b.2 := hy
      obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (sub_pos.mpr hy')
      refine ⟨max n₀ (Encodable.encode b), b, ⟨hEb, le_max_right _ _⟩, ?_⟩
      rw [Metric.mem_ball]
      have hle : (n₀ : ℝ) ≤ (max n₀ (Encodable.encode b) : ℕ) := by
        exact_mod_cast le_max_left _ _
      have : 1 / (((max n₀ (Encodable.encode b) : ℕ) : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
  have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion] at hlim
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 r hr).exists
  let L : List (ℕ × ℚ) :=
    (hS n).toFinset.toList.map fun b ↦ (b.1, b.2 - 1 / ((n : ℚ) + 1))
  have hLW : ballUnion P L = W n := by
    ext y
    simp only [ballUnion, L, W, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset,
      mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, hy⟩
      refine ⟨b, hb, ?_⟩
      simpa [basicBall] using hy
    · rintro ⟨b, hb, hy⟩
      refine ⟨_, ⟨b, hb, rfl⟩, ?_⟩
      simpa [basicBall] using hy
  refine ⟨L, ?_, hLW ▸ hn⟩
  intro b' hb' y hy
  simp only [L, List.mem_map, Finset.mem_toList, Set.Finite.mem_toFinset] at hb'
  obtain ⟨b, ⟨hEb, -⟩, rfl⟩ := hb'
  refine mem_iUnion₂.mpr ⟨b, hEb, ?_⟩
  change dist y (P.ι b.1) < b.2
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  push_cast at hy
  rw [dist_comm]
  linarith


variable [BorelSpace X]

/-- Core of (I2′): for rationals `q < μ(U)` and `η > 0` with `η/8 ≤ q`, the orbit of a
random point visits `U` at least `(1 - η/2)(q - η/8) n - N` times before time `n`, for some `N`
and all `n`. -/
theorem typical_visitCount_lower_of_random (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (hT : Ergodic T μ) {U : Set X} (hU : IsCeOpenIn P A U) {x : X}
    (hx : x ∈ randomPoints P A μ) {q η : ℚ} (hη : 0 < η) (hqη : η / 8 ≤ q)
    (hq : ENNReal.ofReal q < μ U) :
    ∃ N : ℕ, ∀ n : ℕ, (1 - (η : ℝ) / 2) * ((q : ℝ) - η / 8) * n - N ≤
      typicalVisitCount T U n x := by
  obtain ⟨hP, hTA, hμ⟩ := hA
  have hTmp := hT.toMeasurePreserving
  obtain ⟨L, hLU, hLμ⟩ := typical_exists_ballList P hU hq
  -- the open union `W°` and the closed union `W̄` of the shrunk balls
  set Wo : Set X := ballUnion P L with hWo_def
  set Wc : Set X := ⋃ b ∈ L, closedBowenBall T 1 (P.ι b.1) (b.2 : ℝ) with hWc_def
  have hWoWc : Wo ⊆ Wc := by
    intro y hy
    simp only [hWo_def, ballUnion, mem_iUnion, exists_prop] at hy
    obtain ⟨b, hb, hyb⟩ := hy
    refine mem_iUnion₂.mpr ⟨b, hb, fun k hk ↦ ?_⟩
    obtain rfl : k = 0 := by omega
    have : dist y (P.ι b.1) < b.2 := hyb
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, dist_comm]
    exact this.le
  have hWcU : Wc ⊆ U := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy
    exact hLU b hb y (hyb 0 Nat.one_pos)
  have hWoce : IsCeOpenFamilyIn P A fun _ : Unit ↦ Wo :=
    (ballUnion_ceOpen (P := P) (B := A)).comp (Computable.const L)
  have hWcce : IsCeOpenFamilyIn P A fun _ : Unit ↦ Wcᶜ := by
    have hF : IsCeOpenFamilyIn P A fun u : Unit × (ℕ × ℚ) ↦
        (closedBowenBall T 1 (P.ι u.2.1) (u.2.2 : ℝ))ᶜ :=
      (isCeOpenFamilyIn_compl_closedBowenBall P T A hP hTA).comp
        ((Computable.const 1).pair Computable.snd)
    have h := (hF.biInter_list hP).comp (Computable.id.pair (Computable.const L) :
      Computable fun u : Unit ↦ (u, L))
    convert h using 2 with u
    rw [hWc_def, compl_iUnion₂]
  have hWo_meas : MeasurableSet Wo := (isOpen_of_isCeOpenFamilyIn_typical hWoce ()).measurableSet
  have hWc_meas : MeasurableSet Wc :=
    (isOpen_compl_iff.mp (isOpen_of_isCeOpenFamilyIn_typical hWcce ())).measurableSet
  have hq0 : (0 : ℚ) ≤ q := le_trans (by positivity) hqη
  have hqWo : (q : ℝ) < μ.real Wo :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by exact_mod_cast hq0) (measure_ne_top μ _)).mp hLμ
  -- the good sets `G_N` and the bad sets `B_N`
  set q₁ : ℚ := q - η / 16 with hq₁
  set a : ℚ := q - η / 8 with ha
  let G : ℕ → Set X := fun N ↦ {y | ((q₁ * N : ℚ) : ℝ) < typicalVisitCount T Wo N y}
  let B : ℕ → Set X := fun N ↦ {y | (((1 - a) * N : ℚ) : ℝ) < typicalVisitCount T Wcᶜ N y}
  have hG : IsCeOpenFamilyIn P A G :=
    (isCeOpenFamilyIn_typicalVisitCount_gt hP hTA hWoce).comp ((Computable.const ()).pair
      (Computable.id.pair (computable₂_ratMul.comp (Computable.const q₁)
        computable_nat_to_rat)))
  have hB : IsCeOpenFamilyIn P A B :=
    (isCeOpenFamilyIn_typicalVisitCount_gt hP hTA hWcce).comp ((Computable.const ()).pair
      (Computable.id.pair (computable₂_ratMul.comp (Computable.const (1 - a))
        computable_nat_to_rat)))
  have hB_meas : ∀ N, MeasurableSet (B N) := fun N ↦
    (isOpen_of_isCeOpenFamilyIn_typical hB N).measurableSet
  have hG_meas : ∀ N, MeasurableSet (G N) := fun N ↦
    (isOpen_of_isCeOpenFamilyIn_typical hG N).measurableSet
  -- outside `B_N`, the window of length `N` spends the fraction `a` in `W̄`
  have hcompl : ∀ N y, (typicalVisitCount T Wc N y : ℝ) + typicalVisitCount T Wcᶜ N y = N := by
    intro N y
    exact_mod_cast typicalVisitCount_add_compl T Wc N y
  have hnotB : ∀ N y, y ∉ B N → (a : ℝ) * N ≤ typicalVisitCount T Wc N y := by
    intro N y hy
    simp only [B, mem_ofPred_eq, not_lt] at hy
    push_cast at hy
    linarith [hcompl N y]
  have hBG : ∀ N, B N ⊆ (G N)ᶜ := by
    intro N y hyB hyG
    simp only [B, G, mem_ofPred_eq] at hyB hyG
    push_cast at hyB hyG
    have hmono : (typicalVisitCount T Wo N y : ℝ) ≤ typicalVisitCount T Wc N y := by
      exact_mod_cast typicalVisitCount_mono T hWoWc N y
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hηN : 0 ≤ (η : ℝ) * N := mul_nonneg (by exact_mod_cast hη.le) hN0
    rw [hq₁] at hyG
    rw [ha] at hyB
    push_cast at hyB hyG
    nlinarith [hcompl N y]
  -- the search for `N(m)`
  have hlsc := hμ.lowerSemicomputable_ceOpen hG
  let R : ℕ × ℕ → Prop := fun mN ↦
    1 ≤ mN.2 ∧ (((1 - η / 2 * (2⁻¹ : ℚ) ^ mN.1 : ℚ)) : ℝ) < (μ (G mN.2)).toReal
  have hRre : IsREIn A R := by
    have hδc : Computable fun mN : ℕ × ℕ ↦ (1 - η / 2 * (2⁻¹ : ℚ) ^ mN.1 : ℚ) :=
      computable₂_ratSub.comp (Computable.const 1) (computable₂_ratMul.comp
        (Computable.const (η / 2)) (computable_inv_two_pow.comp Computable.fst))
    exact (isREIn_of_computable_decide (Primrec.nat_le.comp (Primrec.const 1)
      Primrec.snd).decide.to_comp).and
      (hlsc.comp (Computable.snd.pair hδc).computableIn)
  have htot : ∀ m, ∃ N, R (m, N) := by
    intro m
    have hδ : (0 : ℝ) < (η : ℝ) / 2 * (2⁻¹ : ℝ) ^ m := by
      have : (0 : ℝ) < η := by exact_mod_cast hη
      positivity
    have hc : ((q₁ : ℚ) : ℝ) < μ.real Wo := by
      rw [hq₁]
      push_cast
      have : (0 : ℝ) < η := by exact_mod_cast hη
      linarith
    obtain ⟨N, hN1, hN⟩ := typical_exists_measure_visitCount_gt hT hWo_meas hc hδ
    refine ⟨N, hN1, ?_⟩
    have hGN : G N = {y | ((q₁ : ℚ) : ℝ) * N < typicalVisitCount T Wo N y} := by
      ext y
      simp [G]
    rw [hGN, ← measureReal_def]
    push_cast
    exact hN
  obtain ⟨Nf, hNfc, hNf⟩ := hRre.exists_computableIn_choice htot
  -- the test `E_m`
  let E : ℕ → Set X := fun m ↦
    ⋃ n : ℕ, {y | ((η / 2 * n : ℚ) : ℝ) < typicalVisitCount T (B (Nf m)) n y}
  have hE : IsCeOpenFamilyIn P A E := by
    have h1 := isCeOpenFamilyIn_typicalVisitCount_gt hP hTA hB
    have hg : ComputableIn {charOracle A} fun mn : ℕ × ℕ ↦ (Nf mn.1, mn.2, η / 2 * mn.2) :=
      (hNfc.comp ComputableIn.fst).pair (ComputableIn.snd.pair
        (computable₂_ratMul.comp (Computable.const (η / 2))
          (computable_nat_to_rat.comp Computable.snd)).computableIn)
    exact (h1.compIn hg).iUnion
  have hEμ : ∀ m, μ (E m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    have hη0 : (0 : ℝ) < η / 2 := by
      have : (0 : ℝ) < η := by exact_mod_cast hη
      linarith
    have hEeq : E m = {y | ∃ n : ℕ, (η / 2 : ℝ) * n <
        typicalVisitCount T (B (Nf m)) n y} := by
      ext y
      simp [E]
    have hmax := typical_measure_visitCount_maximal hTmp (hB_meas (Nf m)) hη0
    rw [← hEeq] at hmax
    have hBμ : μ.real (B (Nf m)) ≤ 1 - μ.real (G (Nf m)) := by
      have := measureReal_mono (μ := μ) (hBG (Nf m))
      rwa [measureReal_compl (hG_meas _), probReal_univ] at this
    have hGμ := (hNf m).2
    rw [← measureReal_def] at hGμ
    push_cast at hGμ
    have hreal : μ.real (E m) ≤ (2⁻¹ : ℝ) ^ m := by
      by_contra hcon
      push Not at hcon
      have := mul_lt_mul_of_pos_left hcon hη0
      linarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E m)), ← measureReal_def]
    calc ENNReal.ofReal (μ.real (E m)) ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ m) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = (2 : ℝ≥0∞)⁻¹ ^ m := by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  obtain ⟨m, hm⟩ := hx E ⟨hE, hEμ⟩
  have hxB : ∀ n : ℕ, (typicalVisitCount T (B (Nf m)) n x : ℝ) ≤ (η / 2 : ℝ) * n := by
    intro n
    by_contra hcon
    push Not at hcon
    exact hm (mem_iUnion.mpr ⟨n, by simp only [mem_ofPred_eq]; push_cast; exact hcon⟩)
  refine ⟨Nf m, fun n ↦ ?_⟩
  have hlow := typical_visitCount_lower T (W := Wc) (B := B (Nf m)) (hNf m).1
    (a := a) (θ := η / 2) (by rw [ha]; push_cast; linarith [(by exact_mod_cast hqη :
      (η : ℝ) / 8 ≤ q)]) (hnotB (Nf m)) hxB n
  have hWcUn : (typicalVisitCount T Wc n x : ℝ) ≤ typicalVisitCount T U n x := by
    exact_mod_cast typicalVisitCount_mono T hWcU n x
  rw [ha] at hlow
  push_cast at hlow
  linarith

/-- Input (I2′): a point that is `μ`-random relative to `A` visits every `A`-effectively open set
`U` with lower frequency at least `μ(U)`, for an ergodic `A`-represented map and an `A`-computable
invariant probability measure. Blueprint node `erg:typical`. -/
theorem measure_le_liminf_visitFrequency (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (hT : Ergodic T μ) {U : Set X} (hU : IsCeOpenIn P A U) {x : X}
    (hx : x ∈ randomPoints P A μ) :
    μ U ≤ liminf (fun n : ℕ ↦
      ((({k | k < n ∧ T^[k] x ∈ U} : Set ℕ).ncard : ℝ≥0∞) / n)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  have hr_top : r ≠ ⊤ := hr.ne_top
  obtain ⟨q, hq0, hrq, hqU⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hr
  change r < ENNReal.ofReal q at hrq
  change ENNReal.ofReal q < μ U at hqU
  have hr' : r.toReal < q := (ENNReal.lt_ofReal_iff_toReal_lt hr_top).mp hrq
  have hq1 : (q : ℝ) < 1 := ENNReal.ofReal_lt_one.mp (hqU.trans_le prob_le_one)
  have hr0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  obtain ⟨η, hη0, hηlt⟩ := exists_rat_btwn (lt_min (sub_pos.mpr hr') one_pos)
  have hηq : (η : ℝ) < q - r.toReal := hηlt.trans_le (min_le_left _ _)
  have hη1 : (η : ℝ) < 1 := hηlt.trans_le (min_le_right _ _)
  have hηpos : (0 : ℚ) < η := by exact_mod_cast hη0
  have hqη : η / 8 ≤ q := by
    have : (η : ℝ) / 8 ≤ q := by linarith
    exact_mod_cast this
  obtain ⟨N, hN⟩ := typical_visitCount_lower_of_random P T A μ hA hT hU hx hηpos hqη hqU
  set c : ℝ := (1 - (η : ℝ) / 2) * ((q : ℝ) - η / 8) with hc
  have hcr : r.toReal < c := by
    rw [hc]
    nlinarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((N : ℝ) / (c - r.toReal))
  refine le_liminf_of_le (by isBoundedDefault) (eventually_atTop.mpr ⟨n₀ + 1, fun n hn ↦ ?_⟩)
  have hn1 : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast le_of_add_le_right hn
    linarith
  have hnn₀ : (n₀ : ℝ) ≤ n := by exact_mod_cast le_of_add_le_left hn
  have hcr' : 0 < c - r.toReal := sub_pos.mpr hcr
  have hNle : (N : ℝ) ≤ (c - r.toReal) * n := by
    have := (div_lt_iff₀ hcr').mp (hn₀.trans_le hnn₀)
    linarith
  have hcount : r.toReal * n ≤ typicalVisitCount T U n x := by
    have := hN n
    nlinarith
  rw [ncard_eq_typicalVisitCount, ← ENNReal.ofReal_toReal hr_top, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_div_of_pos hn1]
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hn1).mpr hcount)

/-- Real form of (I2′): for every `ε > 0`, eventually the visit frequency of a random point to an
effectively open set `U` exceeds `μ(U) - ε`. -/
theorem typical_eventually_lt_visitFrequency (P : Presentation X) (T : X → X) (A : Set ℕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (hT : Ergodic T μ) {U : Set X} (hU : IsCeOpenIn P A U) {x : X}
    (hx : x ∈ randomPoints P A μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (μ U).toReal - ε < (typicalVisitCount T U n x : ℝ) / n := by
  by_cases hneg : (μ U).toReal - ε < 0
  · exact Eventually.of_forall fun n ↦ hneg.trans_le (by positivity)
  push Not at hneg
  have hlt : ENNReal.ofReal ((μ U).toReal - ε) < μ U := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hneg (measure_ne_top μ U)]
    linarith
  have hev := eventually_lt_of_lt_liminf
    (hlt.trans_le (measure_le_liminf_visitFrequency P T A μ hA hT hU hx)) (by isBoundedDefault)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [ncard_eq_typicalVisitCount, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_div_of_pos hn0] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1

omit [MeasurableSpace X] [BorelSpace X] in
/-- A member of a uniformly c.e. open family is c.e. open. -/
theorem isCeOpenIn_of_isCeOpenFamilyIn_typical {P : Presentation X} {A : Set ℕ} {ι : Type*}
    [Primcodable ι] {V : ι → Set X} (hV : IsCeOpenFamilyIn P A V) (i : ι) :
    IsCeOpenIn P A (V i) := by
  obtain ⟨E, hE, hVE⟩ := hV
  exact ⟨fun b ↦ E (i, b), hE.comp ((Computable.const i).pair Computable.id).computableIn,
    hVE i⟩

/-- The itinerary of a random point through a computable partition is generic for the coded
measure. Blueprint node `erg:typical`. -/
theorem isGenericPoint_symbolicCode {p : ℕ} [NeZero p] (P : Presentation X) (T : X → X)
    (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P T μ A)
    (hT : Ergodic T μ) {U : Fin p → Set X} (hU : IsComputablePartitionIn P A μ U) {x : X}
    (hx : x ∈ randomPoints P A μ) :
    IsGenericPoint (codedMeasure μ T U) (symbolicCode T U x) := by
  classical
  intro k w
  have hTmp := hT.toMeasurePreserving
  rw [codedMeasure_wordCylinder hTmp hU w]
  set O : (Fin k → Fin p) → Set X := Ergodic.refinement T U k with hO_def
  -- the cells are effectively open
  have hOce : ∀ w', IsCeOpenIn P A (O w') := by
    intro w'
    have hF : IsCeOpenFamilyIn P A fun u : Unit × (ℕ × Fin p) ↦ T^[u.2.1] ⁻¹' U u.2.2 :=
      (isCeOpenFamilyIn_iterate_preimage_typical hA.1 hA.2.1 hU.1).comp
        ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))
    have h := isCeOpenIn_of_isCeOpenFamilyIn_typical (hF.biInter_list hA.1)
      ((), List.ofFn fun i : Fin k ↦ ((i : ℕ), w' i))
    convert h using 1
    ext y
    simp only [hO_def, Ergodic.refinement, mem_iInter, mem_preimage, List.mem_ofFn]
    constructor
    · rintro hy e ⟨i, rfl⟩
      exact hy i
    · intro hy i
      exact hy _ ⟨i, rfl⟩
  have hO_meas : ∀ w', MeasurableSet (O w') := by
    intro w'
    obtain ⟨E, -, hE⟩ := hOce w'
    rw [hE]
    exact (isOpen_biUnion fun b _ ↦ Metric.isOpen_ball).measurableSet
  -- the cells are disjoint and cover almost everything
  have hdisj : Pairwise (Function.onFun Disjoint O) := by
    intro w₁ w₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy₁ hy₂
    apply hne
    funext i
    simp only [hO_def, Ergodic.refinement, mem_iInter, mem_preimage] at hy₁ hy₂
    by_contra hi
    exact Set.disjoint_left.mp (hU.2.1 hi) (hy₁ i) (hy₂ i)
  have hsum1 : ∑ w', (μ (O w')).toReal = 1 := by
    have hcover : (⋃ w', O w')ᶜ ⊆ ⋃ i : Fin k, T^[i] ⁻¹' (⋃ j, U j)ᶜ := by
      intro y hy
      by_contra hcon
      have hcon' : ∀ i : Fin k, ∃ j, T^[i] y ∈ U j := by
        intro i
        by_contra h
        exact hcon (mem_iUnion.mpr ⟨i, by simpa using h⟩)
      refine hy (mem_iUnion.mpr ⟨fun i ↦ (hcon' i).choose, ?_⟩)
      simp only [hO_def, Ergodic.refinement, mem_iInter, mem_preimage]
      exact fun i ↦ (hcon' i).choose_spec
    have hnull : μ (⋃ w', O w')ᶜ = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun i ↦ ?_)
      have hUm : MeasurableSet (⋃ j, U j)ᶜ :=
        (MeasurableSet.iUnion fun j ↦
          (isOpen_of_isCeOpenFamilyIn_typical hU.1 j).measurableSet).compl
      rw [(hTmp.iterate i).measure_preimage hUm.nullMeasurableSet]
      exact hU.2.2
    have h1 : μ (⋃ w', O w') = 1 :=
      (prob_compl_eq_zero_iff (MeasurableSet.iUnion hO_meas)).mp hnull
    rw [measure_iUnion hdisj hO_meas, tsum_fintype] at h1
    rw [← ENNReal.toReal_sum fun w' _ ↦ measure_ne_top μ (O w'), h1, ENNReal.toReal_one]
  -- word counts and visit counts
  set c : ℕ → Fin k → Fin p := fun j i ↦ symbolicCode T U x (j + i) with hc_def
  set f : (Fin k → Fin p) → ℕ → ℝ := fun w' n ↦
    (({j | j < n ∧ ∀ i : Fin k, symbolicCode T U x (j + i) = w' i} : Set ℕ).ncard : ℝ) / n
    with hf_def
  have hfin : ∀ w' n, ({j | j < n ∧ ∀ i : Fin k, symbolicCode T U x (j + i) = w' i} :
      Set ℕ) = ↑((Finset.range n).filter fun j ↦ c j = w') := by
    intro w' n
    ext j
    simp only [mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, hc_def, funext_iff]
  have hsumf : ∀ n, 1 ≤ n → ∑ w', f w' n = 1 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hf_def, hfin, Set.ncard_coe_finset]
    rw [← Finset.sum_div, div_eq_one_iff_eq hn0.ne']
    have := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.range n)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [Finset.card_range] at this
    exact_mod_cast this.symm
  have hlow : ∀ w', ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (μ (O w')).toReal - ε < f w' n := by
    intro w' ε hε
    filter_upwards [typical_eventually_lt_visitFrequency P T A μ hA hT (hOce w') hx hε]
      with n hn
    refine hn.trans_le (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n))
    rw [← ncard_eq_typicalVisitCount]
    refine Nat.cast_le.mpr (Set.ncard_le_ncard (fun j hj ↦ ⟨hj.1, fun i ↦ ?_⟩)
      ((Set.finite_lt_nat n).subset fun j hj ↦ hj.1))
    obtain ⟨hjn, hjO⟩ := hj
    simp only [hO_def, Ergodic.refinement, mem_iInter, mem_preimage] at hjO
    have hmem : T^[j + i] x ∈ U (w' i) := by
      rw [add_comm, Function.iterate_add_apply]
      exact hjO i
    have hex : ∃ l, T^[j + i] x ∈ U l := ⟨w' i, hmem⟩
    simp only [symbolicCode, hex, ↓reduceDIte]
    by_contra hne
    exact Set.disjoint_left.mp (hU.2.1 hne) hex.choose_spec hmem
  rw [tendsto_order]
  constructor
  · intro a' ha'
    filter_upwards [hlow w _ (sub_pos.mpr ha')] with n hn
    simpa [hf_def] using hn
  · intro b' hb'
    have hK : (0 : ℝ) < Fintype.card (Fin k → Fin p) := by exact_mod_cast Fintype.card_pos
    set ε := (b' - (μ (O w)).toReal) / Fintype.card (Fin k → Fin p) with hε_def
    have hε : 0 < ε := div_pos (sub_pos.mpr hb') hK
    have hall : ∀ᶠ n : ℕ in atTop, ∀ w', (μ (O w')).toReal - ε < f w' n :=
      eventually_all.mpr fun w' ↦ hlow w' ε hε
    filter_upwards [hall, eventually_ge_atTop 1] with n hn hn1
    have hsum : ∑ w', (f w' n - ((μ (O w')).toReal - ε)) =
        Fintype.card (Fin k → Fin p) * ε := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsumf n hn1, hsum1]
      simp
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun w' ↦ f w' n - ((μ (O w')).toReal - ε)) (fun w' _ ↦ (sub_pos.mpr (hn w')).le)
      (Finset.mem_univ w)
    rw [hsum] at hsingle
    have hKε : (Fintype.card (Fin k → Fin p) : ℝ) * ε = b' - (μ (O w)).toReal := by
      rw [hε_def]
      field_simp
    change f w n < b'
    nlinarith

end Kolmogorov.PointToSet
