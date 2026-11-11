/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Shift
import KolmogorovMathlib.PointToSet.Measure.EssentialBounds
import KolmogorovMathlib.PointToSet.Measure.Pointwise

/-!
# Martin-Löf randomness is not enough in Theorem 4.3(b), (c) (Example 5.5)

Question 4.5 of E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random
points*, asks whether the supremum of the upper orbit complexity over the random points can
exceed the essential supremum of `h̄_μ`. Example 5.5 answers yes, on the full shift
`({0,1}^ℕ, σ)` with the metric `d_{1/2}`:

1. there is a computable purely atomic measure `μ` with a `μ`-random point `z` such that
   `K̄(z, σ) = 1` although `h̄_μ(σ, x) = 0` almost everywhere;
2. there is a computable measure `μ'` with `h̲_{μ'}(σ, x) = 1` almost everywhere and a
   `μ'`-random point of lower complexity `0`.

So the optimisation over oracles cannot be dropped in Theorem 4.3(b), nor in (c) for the lower
complexity. The construction uses a left-c.e. `λ`-random real `Ω` and a computable map `f` of
Cantor space with `μ = λ ∘ f⁻¹`.

## Formalisation

"Computable" is `IsMeasureAdmissible P shiftMap μ ∅`: the empty oracle computes the metric table
of the presentation `P`, represents the shift and computes the measure; "random" is
`randomPoints P ∅ μ`. The presentation `P` of Cantor space (with the metric `cantorMetricSpace`)
is quantified existentially: the library has no fixed computable presentation of Cantor space
(the one in `PointToSet/SymbolicSet.lean` is private and not chosen computably).

* `exists_countable_atomic_random_upperLocalEntropy_eq_one`,
  `exists_random_lowerLocalEntropy_eq_zero` — the two constructions, reduced to their core
  (tracked `sorry`s, external input: the `Ω` construction).
* `exampleFiveFive_upper`, `exampleFiveFive_lower` — Example 5.5 (1), (2) in the vocabulary of
  Theorem 4.3, derived from the cores.
* `exists_iSup_randomPoints_gt_essSup`, `not_forall_iSup_randomPoints_eq_essSup`,
  `exists_iInf_randomPoints_lt_essInf`, `not_forall_iInf_randomPoints_eq_essInf` — the oracle
  cannot be fixed in Theorem 4.3(b), (c).

Proved measure-theoretic input:

* `localEntropy_eq_zero_of_measure_singleton_ne_zero`: at an atom both local entropies vanish;
* `ae_localEntropy_eq_zero_of_countable`: a measure carried by a countable set has `Φ_μ = (0, 0)`
  almost everywhere, hence all four essential bounds vanish (`essBounds_eq_zero_of_countable`);
* `countable_setOf_eventually_false`, `exists_countable_map_compl_eq_zero`: the image of a
  measure under a map whose values are almost surely eventually `0` is carried by a countable set;
* `uniformMeasure_singleton`: the fair-coin measure has no atoms;
* `localEntropy_shiftMap_le_one_of_le_cylinder`, `pow_le_map_uniformMeasure_cylinder`: an image
  `λ ∘ f⁻¹` under a causal map has local entropies at most `1` at every image point;
* `one_le_upperLocalEntropy_of_frequently`: the lower bound `h̄_μ(σ, z) ≥ 1` from a frequent
  cylinder estimate `μ[z↾n] ≤ 2^{-(1-δ) n}`.

Remark 4.4 and the weak-2-randomness part of the answer to Question 4.5 are not stated.

Blueprint node `meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### Atoms have local entropies `(0, 0)` -/

section atoms

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- At an atom of `μ` both local entropies vanish: `μ(B_n(x, T, ε)) ≥ μ{x} > 0` for all `n`, so
`-(1/n) log₂ μ(B_n(x, T, ε)) ≤ -(1/n) log₂ μ{x} → 0` (Example 5.5(1): a purely atomic measure has
`Φ_μ = (0, 0)` at each atom). Blueprint node `meas:examples`. -/
theorem localEntropy_eq_zero_of_measure_singleton_ne_zero (μ : Measure X) (T : X → X) {x : X}
    (hx : μ {x} ≠ 0) : localEntropy μ T x = (0, 0) := by
  have hc : infoBits (μ {x}) ≠ ⊤ := (infoBits_lt_top hx).ne
  have hlim : Tendsto (fun n : ℕ ↦ infoBits (μ {x}) / n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hc)
    simpa [div_eq_mul_inv] using this
  have hsup : ∀ p : ℕ, (localEntropyAt μ T x (dyadicRadius p)).2 = 0 := fun p ↦ by
    refine nonpos_iff_eq_zero.1 ?_
    rw [← hlim.limsup_eq]
    refine limsup_le_limsup (.of_forall fun n ↦ ?_)
    exact ENNReal.div_le_div_right (infoBits_antitone (measure_mono
      (singleton_subset_iff.2 (self_mem_bowenBall T n x _ (dyadicRadius_pos p))))) _
  have hinf : ∀ p : ℕ, (localEntropyAt μ T x (dyadicRadius p)).1 = 0 := fun p ↦
    nonpos_iff_eq_zero.1 (le_trans liminf_le_limsup (hsup p).le)
  simp only [localEntropy, hsup, hinf, iSup_const]

/-- A measure carried by a countable set `S` (`μ Sᶜ = 0`) has local entropies `(0, 0)` almost
everywhere: almost every point is an atom. Blueprint node `meas:examples`. -/
theorem ae_localEntropy_eq_zero_of_countable (μ : Measure X) (T : X → X) {S : Set X}
    (hS : S.Countable) (hSμ : μ Sᶜ = 0) : ∀ᵐ x ∂μ, localEntropy μ T x = (0, 0) := by
  have hatom : ∀ᵐ x ∂μ, μ {x} ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (t := Sᶜ ∪ ⋃ y ∈ S ∩ {y | μ {y} = 0}, {y}) ?_
      (measure_union_null hSμ ((measure_biUnion_null_iff (hS.mono inter_subset_left)).2
        fun y hy ↦ hy.2))
    intro x hx
    simp only [ne_eq, not_not, mem_ofPred_eq] at hx
    by_cases hxS : x ∈ S
    · exact Or.inr (mem_biUnion ⟨hxS, hx⟩ (mem_singleton x))
    · exact Or.inl hxS
  exact hatom.mono fun x hx ↦ localEntropy_eq_zero_of_measure_singleton_ne_zero μ T hx

/-- A nonzero measure carried by a countable set has all four essential bounds of its local
entropies equal to `0`. Blueprint node `meas:examples`. -/
theorem essBounds_eq_zero_of_countable (μ : Measure X) [NeZero μ] (T : X → X) {S : Set X}
    (hS : S.Countable) (hSμ : μ Sᶜ = 0) :
    essSup (fun x ↦ (localEntropy μ T x).1) μ = 0 ∧
      essSup (fun x ↦ (localEntropy μ T x).2) μ = 0 ∧
      essInf (fun x ↦ (localEntropy μ T x).1) μ = 0 ∧
      essInf (fun x ↦ (localEntropy μ T x).2) μ = 0 := by
  have h := ae_localEntropy_eq_zero_of_countable μ T hS hSμ
  have h₁ : (fun x ↦ (localEntropy μ T x).1) =ᵐ[μ] fun _ ↦ (0 : ℝ≥0∞) :=
    h.mono fun x hx ↦ by simp [hx]
  have h₂ : (fun x ↦ (localEntropy μ T x).2) =ᵐ[μ] fun _ ↦ (0 : ℝ≥0∞) :=
    h.mono fun x hx ↦ by simp [hx]
  exact ⟨by rw [essSup_congr_ae h₁, essSup_const' 0], by rw [essSup_congr_ae h₂, essSup_const' 0],
    by rw [essInf_congr_ae h₁, essInf_const' 0], by rw [essInf_congr_ae h₂, essInf_const' 0]⟩

end atoms

/-! ### Images of measures on Cantor space -/

section cantor

attribute [local instance] cantorMetricSpace

/-- The first-difference formula for the Cantor metric, in the form used by `Shift.lean`. -/
private lemma cantor_hd :
    ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
  fun _ _ ↦ cantorMetricSpace_dist_eq

/-- The eventually-`0` binary sequences form a countable set. Blueprint node `meas:examples`. -/
theorem countable_setOf_eventually_false :
    {y : ℕ → Bool | ∀ᶠ n in atTop, y n = false}.Countable := by
  refine (countable_range fun s : Finset ℕ ↦ fun n ↦ decide (n ∈ s)).mono ?_
  intro y hy
  obtain ⟨N, hN⟩ := eventually_atTop.1 hy
  refine ⟨(Finset.range N).filter (fun n ↦ y n = true), funext fun n ↦ ?_⟩
  by_cases hn : n < N
  · cases h : y n <;> simp [hn, h]
  · simp [hn, hN n (not_lt.1 hn)]

/-- Example 5.5(1), measure-theoretic part: if `f(y)` is eventually `0` for `ν`-almost every
`y`, then the image measure `ν ∘ f⁻¹` is carried by a countable set (the eventually-`0`
sequences). Blueprint node `meas:examples`. -/
theorem exists_countable_map_compl_eq_zero (ν : Measure (ℕ → Bool))
    {f : (ℕ → Bool) → ℕ → Bool} (hf : AEMeasurable f ν)
    (h : ∀ᵐ y ∂ν, ∀ᶠ n in atTop, f y n = false) :
    ∃ S : Set (ℕ → Bool), S.Countable ∧ ν.map f Sᶜ = 0 := by
  refine ⟨_, countable_setOf_eventually_false, ?_⟩
  rw [Measure.map_apply_of_aemeasurable hf countable_setOf_eventually_false.measurableSet.compl]
  exact ae_iff.1 h

/-- Example 5.5(1), measure-theoretic part: for a map `f` of Cantor space whose values are
`ν`-almost surely eventually `0`, the image measure `μ = ν ∘ f⁻¹` has `Φ_μ = (0, 0)`
`μ`-almost everywhere. Blueprint node `meas:examples`. -/
theorem ae_localEntropy_map_eq_zero (ν : Measure (ℕ → Bool)) {f : (ℕ → Bool) → ℕ → Bool}
    (hf : AEMeasurable f ν) (h : ∀ᵐ y ∂ν, ∀ᶠ n in atTop, f y n = false) :
    ∀ᵐ x ∂(ν.map f), localEntropy (ν.map f) shiftMap x = (0, 0) := by
  obtain ⟨S, hS, hSμ⟩ := exists_countable_map_compl_eq_zero ν hf h
  exact ae_localEntropy_eq_zero_of_countable _ _ hS hSμ

/-- The fair-coin measure has no atoms. Blueprint node `meas:examples`. -/
theorem uniformMeasure_singleton (y : ℕ → Bool) : uniformMeasure {y} = 0 := by
  have hlim : Tendsto (fun n : ℕ ↦ (2 : ℝ≥0∞)⁻¹ ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  refine nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim fun n ↦ ?_)
  rw [← uniformMeasure_cylinder y n]
  exact measure_mono (singleton_subset_iff.2 (PiNat.self_mem_cylinder y n))

/-- If `μ[z↾n] ≥ 2^{-n}` for every `n`, both local entropies of `μ` at `z` are at most `1`.
Blueprint node `meas:examples`. -/
theorem localEntropy_shiftMap_le_one_of_le_cylinder (μ : Measure (ℕ → Bool)) (z : ℕ → Bool)
    (h : ∀ n, (2 : ℝ≥0∞)⁻¹ ^ n ≤ μ (PiNat.cylinder z n)) :
    (localEntropy μ shiftMap z).1 ≤ 1 ∧ (localEntropy μ shiftMap z).2 ≤ 1 := by
  have h1 := localEntropy_uniformMeasure_shiftMap z
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd] at h1
  have hle : ∀ n : ℕ, infoBits (μ (PiNat.cylinder z n)) / n ≤
      infoBits (uniformMeasure (PiNat.cylinder z n)) / n := fun n ↦
    ENNReal.div_le_div_right (infoBits_antitone (by rw [uniformMeasure_cylinder]; exact h n)) _
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd]
  exact ⟨(liminf_le_liminf (.of_forall hle)).trans (congrArg Prod.fst h1).le,
    (limsup_le_limsup (.of_forall hle)).trans (congrArg Prod.snd h1).le⟩

/-- For a causal map `f` of Cantor space (`f(y)↾n` depends only on `y↾n`), the image
`μ = λ ∘ f⁻¹` of the fair-coin measure satisfies `μ[f(x)↾n] ≥ λ[x↾n] = 2^{-n}`.
Blueprint node `meas:examples`. -/
theorem pow_le_map_uniformMeasure_cylinder {f : (ℕ → Bool) → ℕ → Bool}
    (hf : AEMeasurable f uniformMeasure)
    (hcausal : ∀ x y n, y ∈ PiNat.cylinder x n → f y ∈ PiNat.cylinder (f x) n)
    (x : ℕ → Bool) (n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ n ≤ uniformMeasure.map f (PiNat.cylinder (f x) n) := by
  rw [← uniformMeasure_cylinder x n]
  exact (measure_mono (t := f ⁻¹' PiNat.cylinder (f x) n) fun y hy ↦ hcausal x y n hy).trans
    (Measure.le_map_apply hf _)

/-- For a causal map `f`, the image `μ = λ ∘ f⁻¹` has local entropies at most `1` at every image
point `f(x)` (the upper bound `h̄_μ(σ, z) ≤ 1` of Example 5.5(1)).
Blueprint node `meas:examples`. -/
theorem localEntropy_map_uniformMeasure_le_one {f : (ℕ → Bool) → ℕ → Bool}
    (hf : AEMeasurable f uniformMeasure)
    (hcausal : ∀ x y n, y ∈ PiNat.cylinder x n → f y ∈ PiNat.cylinder (f x) n)
    (x : ℕ → Bool) :
    (localEntropy (uniformMeasure.map f) shiftMap (f x)).1 ≤ 1 ∧
      (localEntropy (uniformMeasure.map f) shiftMap (f x)).2 ≤ 1 :=
  localEntropy_shiftMap_le_one_of_le_cylinder _ _ (pow_le_map_uniformMeasure_cylinder hf hcausal x)

/-- If for every `δ > 0` there are infinitely many `n` with `μ[z↾n] ≤ 2^{-(1-δ) n}`, then
`h̄_μ(σ, z) ≥ 1` (the lower bound of Example 5.5(1), where `μ[z↾N_{i+1}] ≤ 2^{-(N_{i+1} - N_i)}`
for infinitely many `i` and `N_i / N_{i+1} → 0`). Blueprint node `meas:examples`. -/
theorem one_le_upperLocalEntropy_of_frequently (μ : Measure (ℕ → Bool)) (z : ℕ → Bool)
    (h : ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop,
      μ (PiNat.cylinder z n) ≤ ENNReal.ofReal ((2 : ℝ) ^ (-((1 - δ) * n)))) :
    1 ≤ (localEntropy μ shiftMap z).2 := by
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) cantor_hd]
  refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
  have hct : c ≠ ⊤ := ne_top_of_lt hc
  have hc1 : c.toReal < 1 := by
    have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hc
    simpa using this
  have hfreq := h (1 - c.toReal) (by linarith)
  refine le_limsup_of_frequently_le ((hfreq.and_eventually (eventually_ge_atTop 1)).mono ?_)
  rintro n ⟨hn, hn1⟩
  have hs : 1 - (1 - c.toReal) = c.toReal := by ring
  rw [hs] at hn
  have hinfo := le_infoBits_of_le_rpow hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_pos.trans_le hn1).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))]
  refine le_trans (le_of_eq ?_) hinfo
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hct, ENNReal.ofReal_natCast]

end cantor

/-! ### Example 5.5 -/

section example55

attribute [local instance] cantorMetricSpace

/-- Example 5.5(1), core construction. Let `Ω` be a left-c.e. `λ`-random real with computable
approximations `Ω_t ↑ Ω`, `S_n = {Ω_t↾n : t > n}`, `(σ_i)` a computable enumeration of `⋃ S_n`,
`E_i = [σ_i]`, `N_1 = |σ_1|`, `N_{i+1} ≥ (i+1) max(N_i, |σ_{i+1}|)`, `J_i = [N_i, N_{i+1})`, and
`f(y)↾J_i = y↾J_i` if `y ∈ E_i`, `0^{|J_i|}` otherwise. Then `μ = λ ∘ f⁻¹` is computable, carried
by the countable set of eventually-`0` sequences, and `z = f(Ω)` is `μ`-random with
`h̄_μ(σ, z) = 1`.

Divergences from the paper: the presentation `P` of Cantor space is existential; "computable"
is `IsMeasureAdmissible P shiftMap μ ∅`, "random" is `randomPoints P ∅ μ`; the conclusion is
stated with the upper *local entropy* at `z` (the paper then passes to `K̄(z, σ)` by
Theorem 3.3, which is done in `exampleFiveFive_upper`). Blueprint node `meas:examples`. -/
theorem exists_countable_atomic_random_upperLocalEntropy_eq_one :
    ∃ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)), IsProbabilityMeasure μ ∧
      IsMeasureAdmissible P shiftMap μ ∅ ∧
      (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
      ∃ z ∈ randomPoints P ∅ μ, (localEntropy μ shiftMap z).2 = 1 := by
  -- TODO(sorry): external input — the Ω construction of Example 5.5(1): a computable
  -- presentation of Cantor space, computability of `λ ∘ f⁻¹` for the computable causal map `f`,
  -- preservation of randomness under computable maps in the chapter's sense of randomness
  -- (relating `randomPoints` with `IsMartinLofRandom` and `omega_binary_isMartinLofRandom`),
  -- `f(y)` eventually `0` for `y ≠ Ω`, and the cylinder estimate at `f(Ω)`.
  sorry

/-- Example 5.5(2), core construction. With the notation of
`exists_countable_atomic_random_upperLocalEntropy_eq_one`, let `f'(y)↾J_i = 0^{|J_i|}` if
`y ∈ E_i` and `y↾J_i` otherwise. Then `μ' = λ ∘ f'⁻¹` is computable, `Φ_{μ'} = (1, 1)`
`μ'`-almost everywhere, and `z' = f'(Ω)` is `μ'`-random with `h̲_{μ'}(σ, z') = 0`, since
`μ'[z'↾N_{i+1}] ≥ 2^{-N_i}` for the infinitely many `i` with `Ω ∈ E_i`.

Divergences from the paper: as for Example 5.5(1); the conclusion is stated with the lower
local entropy at `z'`. Blueprint node `meas:examples`. -/
theorem exists_random_lowerLocalEntropy_eq_zero :
    ∃ (P : Presentation (ℕ → Bool)) (μ' : Measure (ℕ → Bool)), IsProbabilityMeasure μ' ∧
      IsMeasureAdmissible P shiftMap μ' ∅ ∧
      (∀ᵐ x ∂μ', localEntropy μ' shiftMap x = (1, 1)) ∧
      ∃ z' ∈ randomPoints P ∅ μ', (localEntropy μ' shiftMap z').1 = 0 := by
  -- TODO(sorry): external input — the Ω construction of Example 5.5(2): a computable
  -- presentation of Cantor space, computability of `λ ∘ f'⁻¹`, preservation of randomness under
  -- computable maps in the chapter's sense, the estimate `-log₂ μ'[f'(y)↾n] ≥ n - O(log n)` for
  -- `λ`-almost every `y`, and the cylinder estimate at `f'(Ω)`.
  sorry

/-- Example 5.5(1): there are a presentation `P` of Cantor space and a probability measure `μ`
computable from the empty oracle, carried by a countable set, with `Φ_μ = (0, 0)` almost
everywhere (so `ess sup h̄_μ = 0`), and a `μ`-random point `z` which is not an atom and has
upper orbit complexity `K̄(z, σ) = 1`; hence `ess sup h̄_μ < sup_{x ∈ R^μ} K̄(x, σ)`.

Divergences from the paper: `P` is existential (see the module docstring); the paper's
"computable" and "random" are `IsMeasureAdmissible P shiftMap μ ∅` and `randomPoints P ∅ μ`.
Proved from `exists_countable_atomic_random_upperLocalEntropy_eq_one`.
Blueprint node `meas:examples`. -/
theorem exampleFiveFive_upper :
    ∃ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)), IsProbabilityMeasure μ ∧
      IsMeasureAdmissible P shiftMap μ ∅ ∧
      (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
      (∀ᵐ x ∂μ, localEntropy μ shiftMap x = (0, 0)) ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ = 0 ∧
      (∃ z ∈ randomPoints P ∅ μ, μ {z} = 0 ∧ (orbitComplexities P shiftMap ∅ z).2 = 1) ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ <
        ⨆ x ∈ randomPoints P ∅ μ, (orbitComplexities P shiftMap ∅ x).2 := by
  obtain ⟨P, μ, hμ, hA, ⟨S, hS, hSμ⟩, z, hz, hz1⟩ :=
    exists_countable_atomic_random_upperLocalEntropy_eq_one
  have hae := ae_localEntropy_eq_zero_of_countable μ shiftMap hS hSμ
  have hess := (essBounds_eq_zero_of_countable μ shiftMap hS hSμ).2.1
  have hK : (orbitComplexities P shiftMap ∅ z).2 = 1 := by
    rw [orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor ∅ μ hA hz]
    exact hz1
  have hatom : μ {z} = 0 := by
    by_contra h
    rw [localEntropy_eq_zero_of_measure_singleton_ne_zero μ shiftMap h] at hz1
    exact zero_ne_one hz1
  refine ⟨P, μ, hμ, hA, ⟨S, hS, hSμ⟩, hae, hess, ⟨z, hz, hatom, hK⟩, ?_⟩
  rw [hess]
  exact zero_lt_one.trans_le
    (hK ▸ le_iSup₂ (f := fun x _ ↦ (orbitComplexities P shiftMap ∅ x).2) z hz)

/-- Example 5.5(2): there are a presentation `P` of Cantor space and a probability measure `μ'`
computable from the empty oracle with `Φ_{μ'} = (1, 1)` almost everywhere, so
`ess inf h̲_{μ'} = 1`, and a `μ'`-random point `z'` of lower orbit complexity `K̲(z', σ) = 0`;
hence `inf_{x ∈ R^{μ'}} K̲(x, σ) < ess inf h̲_{μ'}`.

Divergences from the paper: as for `exampleFiveFive_upper`. Proved from
`exists_random_lowerLocalEntropy_eq_zero`. Blueprint node `meas:examples`. -/
theorem exampleFiveFive_lower :
    ∃ (P : Presentation (ℕ → Bool)) (μ' : Measure (ℕ → Bool)), IsProbabilityMeasure μ' ∧
      IsMeasureAdmissible P shiftMap μ' ∅ ∧
      (∀ᵐ x ∂μ', localEntropy μ' shiftMap x = (1, 1)) ∧
      essInf (fun x ↦ (localEntropy μ' shiftMap x).1) μ' = 1 ∧
      (∃ z' ∈ randomPoints P ∅ μ', (orbitComplexities P shiftMap ∅ z').1 = 0) ∧
      ⨅ x ∈ randomPoints P ∅ μ', (orbitComplexities P shiftMap ∅ x).1 <
        essInf (fun x ↦ (localEntropy μ' shiftMap x).1) μ' := by
  obtain ⟨P, μ', hμ, hA, hae, z', hz, hz0⟩ := exists_random_lowerLocalEntropy_eq_zero
  have hess : essInf (fun x ↦ (localEntropy μ' shiftMap x).1) μ' = 1 := by
    rw [essInf_congr_ae (g := fun _ ↦ (1 : ℝ≥0∞)) (hae.mono fun x hx ↦ by simp [hx]),
      essInf_const' 1]
  have hK : (orbitComplexities P shiftMap ∅ z').1 = 0 := by
    rw [orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_cantor ∅ μ' hA hz]
    exact hz0
  refine ⟨P, μ', hμ, hA, hae, hess, ⟨z', hz, hK⟩, ?_⟩
  rw [hess]
  exact (hK ▸ iInf₂_le (f := fun x _ ↦ (orbitComplexities P shiftMap ∅ x).1) z' hz).trans_lt
    zero_lt_one

/-! ### The oracle cannot be fixed in Theorem 4.3(b), (c) -/

/-- Consequence of Example 5.5(1) for Theorem 4.3(b): for a fixed admissible oracle `A` the
supremum of the upper orbit complexity over the `A`-random points can exceed `ess sup h̄_μ`
(compare `essSup_upperLocalEntropy_le_iSup_randomPoints`, which gives `≤` for every admissible
`A`). Blueprint node `meas:examples`. -/
theorem exists_iSup_randomPoints_gt_essSup :
    ∃ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ ∧ IsMeasureAdmissible P shiftMap μ A ∧
      essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ <
        ⨆ x ∈ randomPoints P A μ, (orbitComplexities P shiftMap A x).2 := by
  obtain ⟨P, μ, hμ, hA, -, -, -, -, hlt⟩ := exampleFiveFive_upper
  exact ⟨P, μ, ∅, hμ, hA, hlt⟩

/-- The optimisation over oracles cannot be dropped in Theorem 4.3(b): it is not true that
`ess sup h̄_μ = sup_{x ∈ R_A} K̄^A(x, σ)` for every admissible oracle `A`, already on Cantor space
with the shift. Blueprint node `meas:examples`. -/
theorem not_forall_iSup_randomPoints_eq_essSup :
    ¬ ∀ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ → IsMeasureAdmissible P shiftMap μ A →
        ⨆ x ∈ randomPoints P A μ, (orbitComplexities P shiftMap A x).2 =
          essSup (fun x ↦ (localEntropy μ shiftMap x).2) μ := by
  intro h
  obtain ⟨P, μ, A, hμ, hA, hlt⟩ := exists_iSup_randomPoints_gt_essSup
  exact hlt.ne' (h P μ A hμ hA)

/-- Consequence of Example 5.5(2) for Theorem 4.3(c): for a fixed admissible oracle `A` the
infimum of the lower orbit complexity over the `A`-random points can be below `ess inf h̲_μ`
(compare `iInf_randomPoints_orbitComplexities_le_essInf`). Blueprint node `meas:examples`. -/
theorem exists_iInf_randomPoints_lt_essInf :
    ∃ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ ∧ IsMeasureAdmissible P shiftMap μ A ∧
      ⨅ x ∈ randomPoints P A μ, (orbitComplexities P shiftMap A x).1 <
        essInf (fun x ↦ (localEntropy μ shiftMap x).1) μ := by
  obtain ⟨P, μ, hμ, hA, -, -, -, hlt⟩ := exampleFiveFive_lower
  exact ⟨P, μ, ∅, hμ, hA, hlt⟩

/-- The optimisation over oracles cannot be dropped in Theorem 4.3(c) for the lower
complexity: it is not true that `ess inf h̲_μ = inf_{x ∈ R_A} K̲^A(x, σ)` for every admissible
oracle `A`. Blueprint node `meas:examples`. -/
theorem not_forall_iInf_randomPoints_eq_essInf :
    ¬ ∀ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ → IsMeasureAdmissible P shiftMap μ A →
        ⨅ x ∈ randomPoints P A μ, (orbitComplexities P shiftMap A x).1 =
          essInf (fun x ↦ (localEntropy μ shiftMap x).1) μ := by
  intro h
  obtain ⟨P, μ, A, hμ, hA, hlt⟩ := exists_iInf_randomPoints_lt_essInf
  exact hlt.ne (h P μ A hμ hA)

end example55

end Kolmogorov.PointToSet
