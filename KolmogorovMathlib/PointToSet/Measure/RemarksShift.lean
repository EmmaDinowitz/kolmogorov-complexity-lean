/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftGeneric
import KolmogorovMathlib.PointToSet.Measure.IntegralAffinity
import KolmogorovMathlib.PointToSet.Measure.EntropyLaw
import KolmogorovMathlib.PointToSet.Measure.UniversalMeasure
import KolmogorovMathlib.MonotoneComplexity.APrioriComplexity

/-!
# Remarks 3.4, 6.6, 6.7 and 7.11: shifts, the a priori probability and invariant measures

The remarks of E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random
points*, that touch material outside the chapter: the Levin–Schnorr estimate on Cantor space,
the universal semimeasure, the Brin–Katok formula and the effective ergodic theorem.

## Remark 3.4 (what each half of Theorem 3.3 uses)

On Cantor space with `d(x, y) = 2^{-firstDiff x y}` the Bowen ball `B_n(x, σ, 1)` is the
cylinder `[x↾n]` (`bowenBall_shiftMap_one_cantor`), so `K_n^A(x, σ, 1)` is the least `K^A(i)`
of an ideal point in `[x↾n]`: the complexity of the cylinder in the chapter's vocabulary.

* (a) What Lemmas 3.1 and 3.2 give, with a change of length:
  `orbitComplexityNat_cylinder_le_infoBits` (coding direction, every point:
  `K([x↾n]) ≤ I_{n+3} + 2 log₂ n + 2 log₂ (I_{n+3} + 2) + c`, `I_m = -log₂ μ[x↾m]`; the shift
  by `3` symbols is the factor `6` that the formal Lemma 3.1 loses in the radius) and
  `infoBits_cylinder_le_orbitComplexityNat_of_mem_randomPoints` (incompressibility direction,
  random points: `I_n ≤ K([x↾(n+1)]) + 2 log₂ n + m`). Proved.
* (b) The exact Levin–Schnorr form `K^A(x↾n) = -log₂ μ[x↾n] + O(log n)` with the complexity of
  the word `x↾n` itself: `oracleComplexity_cantorPrefix_le_infoBits` (every point) and
  `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints` (random points), tracked
  `sorry`s; `abs_oracleComplexity_cantorPrefix_sub_infoBits_le` combines them. The library's
  Levin–Schnorr theorems for computable measures on Cantor space
  (`Kolmogorov.isMartinLofRandom_iff_boundedPrefixDeficiency`,
  `Kolmogorov.isMartinLofRandom_iff_boundedAPrioriDeficiency` in
  `MonotoneComplexity/LevinSchnorr/Criteria.lean`) are related: they use the library's own
  Martin-Löf randomness on Cantor space (`IsMartinLofRandom`, for the empty oracle) and the
  unrelativized prefix, monotone and a priori complexities; they are not bridged here to
  `randomPoints` and `oracleComplexity`.

## Remark 6.6 (the universal semimeasure)

For the empty oracle the library has the continuous a priori probability `M`
(`Kolmogorov.universalContinuousSemimeasure`) and `KA w = -log₂ M(w)`, with both comparisons to
prefix complexity. `abs_oracleComplexity_empty_sub_KA_le`:
`|K(w) + log₂ M(w)| ≤ 2 log₂ |w| + c` for every binary word `w` (proved; `K = K^∅` is
`oracleComplexity ∅`, identified with the library's `KPPlain` of an optimal prefix machine by
`isOptimalPrefixConditional_optimalOraclePrefix_empty`). The consequence "`Ψ^∅` is the pair of
local entropies of `M`" is `orbitComplexities_eq_rates_KA`, proved from the comparison
`universalMeasure_cylinder_comparison_KA` between `m^∅[w]` and `M(w)` (tracked `sorry`).

## Remark 6.7 (invariant measures)

Mathlib has neither the Kolmogorov–Sinai entropy nor the Brin–Katok theorem. The Brin–Katok
theorem is stated in the form available without Kolmogorov–Sinai entropy (tracked `sorry`s):
`ae_localEntropy_fst_eq_snd_of_measurePreserving` (invariant `μ`: lower and upper local
entropies agree almost everywhere) and `ae_localEntropy_eq_of_ergodic` (ergodic `μ`: the local
entropy is almost everywhere the constant `(h, h)`, `h` the Feng–Huang entropy, which stands for
`h_μ(T)`). Proved from them: `ae_entropyLaw_fst_eq_snd` (`Λ_μ` is carried by the diagonal),
`measureEntropy_fst_eq_snd_of_measurePreserving` (its two marginal means agree),
`entropyLaw_sum_ergodic` (`Λ_μ = ∑_j t_j δ_{(h_j, h_j)}` for countably many ergodic components)
and, from Theorem 7.5(b), `entropyLaw_eq_map_of_ergodicDecomposition` (`Λ_μ` is the law of the
entropy of the ergodic component).

## Remark 7.11 (what is known and what is open)

On a finite-alphabet shift with the hypotheses of `ShiftGeneric.lean`:

* `exists_isGenericPoint_of_mem_randomPoints` (V'yugin's effective ergodic theorem, tracked
  `sorry`): every `μ`-random point of a shift-invariant `μ` is generic for a shift-invariant
  probability measure `Q_x`.
* `exists_isGenericPoint_upperOrbitComplexity_le` (proved from it and Proposition 7.10(i)):
  `K̄^A(x, σ) ≤ h_{Q_x}(σ)`; `exists_isGenericPoint_orbitComplexities` adds the conditional
  consequence of Hoyrup's results: if `Q_x` is ergodic and `x` is `Q_x`-random relative to an
  oracle computing `Q_x`, both orbit complexities equal `h_{Q_x}(σ)` (Proposition 7.10(ii)).
* `RandomPointsInErgodicComponents` records the open question of [HoyE] as a proposition (not
  asserted); `localEntropy_eq_shiftEntropy_of_randomPointsInErgodicComponents` proves that a
  positive answer gives the every-point form of Theorem 7.5(b) on shifts.

## Not stated

* Remark 6.6 for a general oracle `A`. It needs the relativized continuous a priori
  probability: lower semicomputable (relative to `A`) continuous semimeasures on binary words,
  the existence of a maximal one `M^A` (the relativized `exists_maximal_lowerSemicomputable…`
  of `MonotoneComplexity/MaximalSemimeasure.lean`), and the relativized comparisons
  `KA^A ≤ K^A + O(1)`, `K^A ≤ KA^A + 2 log₂ |w| + O(1)`. Only the empty oracle is available.
  On a shift over a general finite alphabet the same holds for semimeasures on words over the
  alphabet.
* Remark 7.11, second bullet (Hoyrup's theorems). Stating them needs the space of ergodic
  shift-invariant measures with its topology, the representing measure of the ergodic
  decomposition of `μ` (a measure on that space), its computability relative to `μ`
  ("effectively decomposable"), the case of a representing measure carried by a closed set of
  ergodic measures, and V'yugin's non-effectively decomposable example. None of these exist in
  Mathlib or in this library. Only the conditional consequence quoted above is stated.
* Remark 7.11: the translation of randomness for a non-computable measure into randomness
  relative to an oracle computing it (Reimann–Slaman; equivalent to uniform-test randomness
  by Day–Miller) is granted by the paper; here randomness for `Q_x` is always relative to an
  explicit admissible oracle `B`, which is the form the paper uses.
* The first two sentences of Remark 3.4 are commentary on Theorem 3.3, whose two halves are
  `orbitComplexityAt_le_localEntropyAt` (every point, every measure the oracle computes) and
  `localEntropyAt_le_orbitComplexityAt` (random points).

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

/-- The information of a positive mass at most one, as a real number, is `-log₂` of the mass. -/
private lemma toReal_infoBits {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq1 : q ≤ 1) :
    (infoBits q).toReal = -Real.logb 2 q.toReal := by
  rw [infoBits_of_ne hq0, ENNReal.toReal_ofReal]
  have h1 : q.toReal ≤ 1 := by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hq1
  have := Real.logb_nonpos one_lt_two ENNReal.toReal_nonneg h1
  linarith

/-- `log₂ n ≥ 0` for a natural number `n` (with `log₂ 0 = 0`). -/
private lemma logb_natCast_nonneg (n : ℕ) : 0 ≤ Real.logb 2 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast hn)

/-- The orbit complexity depends on the order and the radius only through the Bowen ball. -/
private lemma orbitComplexityNat_congr_ball {X : Type*} [MetricSpace X] (P : Presentation X)
    (T : X → X) (A : Set ℕ) (x : X) {n n' : ℕ} {r r' : ℝ}
    (h : bowenBall T n x r = bowenBall T n' x r') :
    orbitComplexityNat P T A x n r = orbitComplexityNat P T A x n' r' := by
  simp only [orbitComplexityNat, orbitComplexity, h]

/-! ### Remark 3.4 on Cantor space -/

section cantor

attribute [local instance] cantorMetricSpace

/-- The Cantor metric is the first-difference metric with ratio `1/2`. -/
private lemma cantor_hd :
    ∀ x y : ℕ → Bool, x ≠ y → dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
  fun _ _ ↦ cantorMetricSpace_dist_eq

/-- On Cantor space the Bowen ball of order `n ≥ 1` and radius `1` is the cylinder `[x↾n]`;
hence `orbitComplexityNat P shiftMap A x n 1` is the least `K^A(i)` of an ideal point of the
cylinder `[x↾n]`. Blueprint node `meas:remarks`. -/
theorem bowenBall_shiftMap_one_cantor (x : ℕ → Bool) {n : ℕ} (hn : 1 ≤ n) :
    bowenBall shiftMap n x 1 = PiNat.cylinder x n := by
  simpa using bowenBall_shiftMap_eq_cylinder (β := 1 / 2) (by norm_num) (by norm_num) cantor_hd
    x hn 0

/-- The Bowen ball of order `n ≥ 1` and radius `2^{-k}` is the cylinder `[x↾(n + k)]`. -/
private lemma bowenBall_cantor_pow (x : ℕ → Bool) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    bowenBall shiftMap n x ((1 / 2 : ℝ) ^ k) = PiNat.cylinder x (n + k) :=
  bowenBall_shiftMap_eq_cylinder (β := 1 / 2) (by norm_num) (by norm_num) cantor_hd x hn k

/-- Remark 3.4, coding direction, in the chapter's vocabulary (what Lemma 3.1 gives on Cantor
space): for a measure `μ` of mass at most one computed by `A` there is `c` such that for every
point `x` and every `n ≥ 1` with `μ[x↾(n+3)] > 0`, the complexity of the cylinder `[x↾n]` (the
least `K^A(i)` of an ideal point in it, `bowenBall_shiftMap_one_cantor`) satisfies
`K([x↾n]) ≤ I + 2 log₂ n + 2 log₂ (I + 2) + c`, `I = -log₂ μ[x↾(n+3)]`.

Divergence from the paper: the information is taken at the length `n + 3`, not `n`. The formal
Lemma 3.1 (`coding_by_measure_info`) bounds the complexity at the radius `6ε` by the measure at
the radius `ε`; on Cantor space the factor `6 < 2^3` costs `3` symbols. The exact form without
change of length is `oracleComplexity_cantorPrefix_le_infoBits`. Blueprint node
`meas:remarks`. -/
theorem orbitComplexityNat_cylinder_le_infoBits (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P shiftMap μ A) :
    ∃ c : ℕ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n → μ (PiNat.cylinder x (n + 3)) ≠ 0 →
      (orbitComplexityNat P shiftMap A x n 1 : ℝ) ≤
        (infoBits (μ (PiNat.cylinder x (n + 3)))).toReal + 2 * Real.logb 2 n +
          2 * Real.logb 2 ((infoBits (μ (PiNat.cylinder x (n + 3)))).toReal + 2) + c := by
  obtain ⟨c, hc⟩ := coding_by_measure_info P shiftMap continuous_shiftMap_cantor A μ hμ hA
    (1 / 8) (by norm_num)
  refine ⟨c, fun x n hn h0 ↦ ?_⟩
  have hball : bowenBall shiftMap n x (((1 / 8 : ℚ) : ℝ)) = PiNat.cylinder x (n + 3) := by
    rw [← bowenBall_cantor_pow x hn 3]
    norm_num
  have h := hc x n hn (by rwa [hball])
  rw [hball] at h
  have hmono : orbitComplexityNat P shiftMap A x n 1 ≤
      orbitComplexityNat P shiftMap A x n (6 * ((1 / 8 : ℚ) : ℝ)) :=
    orbitComplexityNat_antitone_radius P continuous_shiftMap_cantor A x n (by norm_num)
      (by norm_num)
  have hq1 : μ (PiNat.cylinder x (n + 3)) ≤ 1 := (measure_mono (subset_univ _)).trans hμ
  rw [toReal_infoBits h0 hq1]
  calc (orbitComplexityNat P shiftMap A x n 1 : ℝ)
      ≤ orbitComplexityNat P shiftMap A x n (6 * ((1 / 8 : ℚ) : ℝ)) := by exact_mod_cast hmono
    _ ≤ _ := h

/-- Remark 3.4, incompressibility direction, in the chapter's vocabulary (what Lemma 3.2 gives
on Cantor space): for a probability measure `μ` computed by `A` and a point `x ∈ R_A^μ` there is
`m` such that for every `n ≥ 1`, `μ[x↾n] > 0` and
`-log₂ μ[x↾n] ≤ K([x↾(n+1)]) + 2 log₂ n + m`, where `K([x↾(n+1)])` is the least `K^A(i)` of an
ideal point in the cylinder `[x↾(n+1)]` (`bowenBall_shiftMap_one_cantor`).

Divergence from the paper: the complexity is that of the cylinder of length `n + 1` (Lemma 3.2
compares the radii `ε` and `2ε`, one symbol on Cantor space). Blueprint node `meas:remarks`. -/
theorem infoBits_cylinder_le_orbitComplexityNat_of_mem_randomPoints
    (P : Presentation (ℕ → Bool)) (A : Set ℕ) (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P shiftMap μ A) {x : ℕ → Bool} (hx : x ∈ randomPoints P A μ) :
    ∃ m : ℕ, ∀ n : ℕ, 1 ≤ n → μ (PiNat.cylinder x n) ≠ 0 ∧
      (infoBits (μ (PiNat.cylinder x n))).toReal ≤
        orbitComplexityNat P shiftMap A x (n + 1) 1 + 2 * Real.logb 2 n + m := by
  obtain ⟨m, hm⟩ := exists_measure_bowenBall_ge_of_mem_randomPoints P shiftMap
    continuous_shiftMap_cantor A μ hA (1 / 2) (by norm_num) hx
  refine ⟨m, fun n hn ↦ ?_⟩
  have h := hm n hn
  have hb2 : bowenBall shiftMap n x (2 * ((1 / 2 : ℚ) : ℝ)) = PiNat.cylinder x n := by
    rw [← bowenBall_shiftMap_one_cantor x hn]
    norm_num
  have hb1 : bowenBall shiftMap n x ((1 / 2 : ℚ) : ℝ) = bowenBall shiftMap (n + 1) x 1 := by
    rw [bowenBall_shiftMap_one_cantor x (by omega), ← bowenBall_cantor_pow x hn 1]
    norm_num
  rw [hb2, orbitComplexityNat_congr_ball P shiftMap A x hb1] at h
  set K := orbitComplexityNat P shiftMap A x (n + 1) 1
  set q := μ (PiNat.cylinder x n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlhs0 : (2 : ℝ≥0∞)⁻¹ ^ (K + m) / (n : ℝ≥0∞) ^ 2 ≠ 0 :=
    (ENNReal.div_pos (by simp) (by simp)).ne'
  have hq0 : q ≠ 0 := fun h0 ↦ hlhs0 (le_antisymm (h0 ▸ h) bot_le)
  refine ⟨hq0, ?_⟩
  have hreal : (2 : ℝ)⁻¹ ^ (K + m) / (n : ℝ) ^ 2 ≤ q.toReal := by
    have := ENNReal.toReal_mono (measure_ne_top μ _) h
    simpa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_inv] using this
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (K + m) / (n : ℝ) ^ 2 := by positivity
  have hlog := Real.logb_le_logb_of_le one_lt_two hpos hreal
  rw [Real.logb_div (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
    Real.logb_inv, Real.logb_self_eq_one one_lt_two] at hlog
  rw [toReal_infoBits hq0 prob_le_one]
  push_cast at hlog ⊢
  linarith

/-- Remark 3.4(b), coding direction of the Levin–Schnorr estimate with the complexity of the
word itself: if `A` computes a measure `μ` of mass at most one and the symbols of the ideal
points of the presentation, then `K^A(x↾n) ≤ -log₂ μ[x↾n] + O(log n)` for every point `x` and
every `n ≥ 1` with `μ[x↾n] > 0` (`x↾n` is the binary word `cantorPrefix x n`).

Added hypothesis (as in `upperOrbitComplexity_le_shiftEntropy`): `hP`, the symbols of the ideal
points are `A`-computable; it relates words to ideal points.

Prerequisites: (1) a cylinder version of Lemma 3.1 without change of scale: the cylinders of
length `n` of measure `> 2^{-k}` are pairwise disjoint, so there are fewer than `2^k` of them and
no greedy selection is needed; the triples `(w, k, n)` with `|w| = n`, `μ[w] > 2^{-k}` form an
`A`-c.e. set (lower semicomputability of `μ[w]` from `IsComputableMeasureIn`, the cylinder
`[w]` being a basic ball about an ideal point found by search using `hP`) of total weight
`∑ 2^{-k} n^{-2} < ∞`, so `oracle_coding_finite_mass` (`Oracle/KraftChaitin.lean`) applies
directly and gives `K^A(⟨w, k, n⟩) ≤ k + 2 log₂ n + O(1)`; (2) `K^A(w) ≤ K^A(⟨w, k, n⟩) + O(1)`
(a computable projection, `oracle_tuple_bounds`). Available: `coding_by_measure`,
`exists_selection` (the version with change of scale), `bowenBall_shiftMap_eq_cylinder`.
Blueprint node `meas:remarks`. -/
theorem oracleComplexity_cantorPrefix_le_infoBits (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P shiftMap μ A) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n → μ (PiNat.cylinder x n) ≠ 0 →
      (oracleComplexity A (cantorPrefix x n) : ℝ) ≤
        (infoBits (μ (PiNat.cylinder x n))).toReal + c * Real.logb 2 n + c := by
  -- TODO(sorry): not yet proved — the cylinder coding theorem without change of scale and the
  -- translation between words and ideal points (see the docstring).
  sorry

/-- Remark 3.4(b), incompressibility direction of the Levin–Schnorr estimate with the
complexity of the word itself: if `A` is admissible for a probability measure `μ` and computes
the symbols of the ideal points, then at every `x ∈ R_A^μ`,
`-log₂ μ[x↾n] ≤ K^A(x↾n) + O(log n)` (in fact `+ O(1)` holds, Levin–Schnorr–Chaitin; the paper
states `O(log n)`).

Added hypothesis: `hP`, as in `oracleComplexity_cantorPrefix_le_infoBits`.

Prerequisites: (1) a cylinder version of the test of Lemma 3.2: the sets
`V_m = ⋃ {[w] : μ[w] < 2^{-K^A(w) - m}}` are uniformly `A`-c.e. open (upper semicomputability of
`K^A`, `isREIn_oracleNatComplexity_lt`, and of `μ[w]`: cylinders are clopen, so
`IsComputableMeasureIn.isREIn_measure_compl_lt` applies to `[w]`) with
`μ(V_m) ≤ ∑_w 2^{-K^A(w) - m} ≤ 2^{-m}` (`oracle_kraft`); a random point leaves some `V_m`
(`not_forall_mem_of_mem_randomPoints`); (2) the translation of `[w]` into a basic ball about an
ideal point found from `w` by search (using `hP`), so that `V_m` is `A`-c.e. open in the sense of
the presentation. Alternatively: (2') `K^A(i) ≤ K^A(w) + O(1)` for an ideal point `P.ι i ∈ [w]`
computed from `w`, together with `infoBits_cylinder_le_orbitComplexityNat_of_mem_randomPoints`
and `K^A(w b) ≤ K^A(w) + O(1)` for a bit `b`. Blueprint node `meas:remarks`. -/
theorem infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints
    (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P shiftMap μ A)
    {x : ℕ → Bool} (hx : x ∈ randomPoints P A μ) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      (infoBits (μ (PiNat.cylinder x n))).toReal ≤
        oracleComplexity A (cantorPrefix x n) + c * Real.logb 2 n + c := by
  -- TODO(sorry): not yet proved — the cylinder version of the test of Lemma 3.2 and the
  -- translation between words and ideal points (see the docstring).
  sorry

/-- Remark 3.4: on Cantor space, at every `μ`-random point relative to an admissible oracle `A`
that computes the symbols of the ideal points, the Levin–Schnorr estimate
`K^A(x↾n) = -log₂ μ[x↾n] + O(log n)` holds. Proved from the two directions
`oracleComplexity_cantorPrefix_le_infoBits` and
`infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints` (both tracked `sorry`s).
Blueprint node `meas:remarks`. -/
theorem abs_oracleComplexity_cantorPrefix_sub_infoBits_le (P : Presentation (ℕ → Bool))
    (A : Set ℕ) (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P shiftMap μ A)
    {x : ℕ → Bool} (hx : x ∈ randomPoints P A μ) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      |(oracleComplexity A (cantorPrefix x n) : ℝ) - (infoBits (μ (PiNat.cylinder x n))).toReal|
        ≤ c * Real.logb 2 n + c := by
  obtain ⟨c₁, h₁⟩ := oracleComplexity_cantorPrefix_le_infoBits P A hP μ prob_le_one hA
  obtain ⟨c₂, h₂⟩ := infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints P A hP μ hA hx
  obtain ⟨m, hm⟩ := infoBits_cylinder_le_orbitComplexityNat_of_mem_randomPoints P A μ hA hx
  refine ⟨max c₁ c₂, fun n hn ↦ ?_⟩
  have hl := logb_natCast_nonneg n
  have e₁ := h₁ x n hn (hm n hn).1
  have e₂ := h₂ n hn
  have k₁ : c₁ * Real.logb 2 n ≤ max c₁ c₂ * Real.logb 2 n :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hl
  have k₂ : c₂ * Real.logb 2 n ≤ max c₁ c₂ * Real.logb 2 n :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hl
  rw [abs_le]
  constructor <;> linarith [le_max_left c₁ c₂, le_max_right c₁ c₂]

/-! ### Remark 6.6 for the empty oracle -/

/-- The optimal oracle prefix machine of the empty oracle is an optimal prefix machine in the
unrelativized sense (as in `OracleSymmetryLower.of_partrec`), so `K^∅ = KPPlain` of it.
Blueprint node `meas:remarks`. -/
theorem isOptimalPrefixConditional_optimalOraclePrefix_empty :
    IsOptimalPrefixConditional (optimalOraclePrefix (∅ : Set ℕ)) := by
  have hA : Partrec (charOracle (∅ : Set ℕ)) := by
    have h : charOracle (∅ : Set ℕ) = ((fun _ ↦ 0 : ℕ → ℕ) : ℕ →. ℕ) := by
      funext n
      simp [charOracle]
    rw [h]
    exact Computable.const 0
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec (∅ : Set ℕ)
  have hUpartrec : isDecompressor (optimalOraclePrefix (∅ : Set ℕ)) := by
    have h : PartrecIn {charOracle (∅ : Set ℕ)} (optimalOraclePrefix ∅) :=
      (isDecompressorIn_iff_partrecIn _ _).mp hUd
    exact RecursiveIn.partrec_of_oracle
      (fun g hg ↦ by rw [Set.mem_singleton_iff.mp hg]; exact hA) h
  refine ⟨⟨hUpartrec, hUp⟩, fun M hM ↦ ?_⟩
  exact hopt M ((isDecompressorIn_iff_partrecIn _ _).mpr
    (relative_closure ∅ M hM.isDecompressor)) hM.isPrefixMachine

/-- Remark 6.6 for the empty oracle: `K(w) = -log₂ M(w) + O(log |w|)` for every binary word `w`,
where `K = K^∅` is prefix complexity (`oracleComplexity ∅`) and `M` is the universal (maximal)
lower semicomputable continuous semimeasure on binary words
(`Kolmogorov.universalContinuousSemimeasure`, the a priori probability; `-log₂ M(w)` is
`Kolmogorov.KA w`). Explicitly `|K(w) + log₂ M(w)| ≤ 2 log₂ |w| + c`.

Divergence from the paper: only the empty oracle and the binary alphabet (the shift is Cantor
space, `M[w]` is `M` of the word `w`); the relativized `M^A` is not available (see the module
docstring, `Not stated`). Proved from `KA_le_KPPlain` and
`KPPlain_le_KA_add_two_mul_log_length`. Blueprint node `meas:remarks`. -/
theorem abs_oracleComplexity_empty_sub_KA_le :
    ∃ c : ℝ, ∀ w : BitString,
      |(oracleComplexity (∅ : Set ℕ) w : ℝ) -
          -Real.logb 2 (universalContinuousSemimeasure w).toReal| ≤
        2 * Real.logb 2 w.length + c := by
  have hU := isOptimalPrefixConditional_optimalOraclePrefix_empty
  obtain ⟨c₁, h₁⟩ := KA_le_KPPlain _ hU
  obtain ⟨c₂, h₂⟩ := KPPlain_le_KA_add_two_mul_log_length _ hU
  refine ⟨max c₁ c₂, fun w ↦ ?_⟩
  have hK : ((KPPlain (optimalOraclePrefix (∅ : Set ℕ)) w).toNat : ℝ) =
      oracleComplexity (∅ : Set ℕ) w := by
    have h : KPPlain (optimalOraclePrefix (∅ : Set ℕ)) w =
        (oracleComplexity (∅ : Set ℕ) w : ENat) :=
      (oraclePrefixComplexity_coe (∅ : Set ℕ) w []).symm
    rw [h, ENat.toNat_natCast]
  have e₁ := h₁ w
  have e₂ := h₂ w
  rw [hK] at e₁ e₂
  have hl := logb_natCast_nonneg w.length
  unfold KA at e₁ e₂
  rw [abs_le]
  constructor <;> linarith [le_max_left c₁ c₂, le_max_right c₁ c₂]

end cantor

end Kolmogorov.PointToSet
