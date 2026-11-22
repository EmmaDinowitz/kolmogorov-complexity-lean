/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.IntegralAffinity
import KolmogorovMathlib.PointToSet.Measure.Ergodic.Proposition710
import KolmogorovMathlib.PointToSet.Measure.Ergodic.BrinKatokNonErgodic
import KolmogorovMathlib.PointToSet.Measure.Ergodic.VyuginGenericity
import KolmogorovMathlib.PointToSet.Measure.Ergodic.CantorLevinSchnorr
import KolmogorovMathlib.PointToSet.Measure.Ergodic.UniversalMeasureWords

/-!
# Remarks 3.4, 6.6, 6.7 and 7.11: shifts, the a priori probability and invariant measures

The remarks of E. Dinowitz, *Entropy of non-invariant measures and orbit complexity of random
points*, that touch material outside the chapter: the Levin–Schnorr estimate on Cantor space,
the universal semimeasure, the Brin–Katok formula and the effective ergodic theorem.

The hypothesis `hP` (symbols of the ideal points computable relative to the oracle) carried by
several statements below holds for every oracle in the standard presentation `cantorPresentation`
of Cantor space; `Ergodic/CantorInstances.lean` states Remarks 3.4, 6.6 and 7.11 (and
Proposition 7.10) there without it.

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
  `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints` (random points), proved in
  `Ergodic/CantorLevinSchnorr.lean`; `abs_oracleComplexity_cantorPrefix_sub_infoBits_le` combines
  them. The library's
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
local entropies of `M`" is `orbitComplexities_eq_rates_KA`
(`K̲(x, σ) = liminf_n KA(x↾n)/n`, `K̄(x, σ) = limsup_n KA(x↾n)/n` at every point, for the
standard computable presentation), proved from Proposition 6.12, the cylinder formula and the
word-level comparison `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le`
(`-log₂ m^A[w] = K^A(w) + O(log |w|)`, proved in `Ergodic/UniversalMeasureWords.lean`).

## Remark 6.7 (invariant measures)

Mathlib has neither the Kolmogorov–Sinai entropy nor the Brin–Katok theorem. The Brin–Katok
theorem is stated in two forms: `ae_localEntropy_fst_eq_snd_of_measurePreserving` (invariant
`μ`: lower and upper local entropies agree almost everywhere; proved from the ergodic
decomposition of `Ergodic/ErgodicDecomposition.lean` and Theorem 7.5(b)) and
`ae_localEntropy_eq_of_ergodic` (ergodic `μ`: the local entropy is
almost everywhere the constant `(h, h)`, `h` the Feng–Huang entropy). The ergodic form is proved
from Theorem 1 of the note *Orbit complexity of Martin-Löf random points equals
entropy* (`Measure/Ergodic/OrbitEntropy.lean`), which also identifies `h` with the
Kolmogorov–Sinai entropy `Ergodic.ksEntropy μ T` (fully proved, Hoyrup's theorem included).
Proved from them: `ae_entropyLaw_fst_eq_snd` (`Λ_μ` is carried by the diagonal),
`measureEntropy_fst_eq_snd_of_measurePreserving` (its two marginal means agree),
`entropyLaw_eq_dirac_of_ergodic` (`Λ_μ = δ_{(h, h)}` for ergodic `μ`),
`entropyLaw_sum_ergodic` (`Λ_μ = ∑_j t_j δ_{(h_j, h_j)}` for countably many ergodic components)
and, from Theorem 7.5(b), `entropyLaw_eq_map_of_ergodicDecomposition` (`Λ_μ` is the law of the
entropy of the ergodic component).

## Remark 7.11 (what is known and what is open)

On a finite-alphabet shift with the hypotheses of `ShiftGeneric.lean`:

* `exists_isGenericPoint_of_mem_randomPoints` (V'yugin's effective ergodic theorem, proved in
  `Ergodic/VyuginGenericity.lean`): every `μ`-random point of a shift-invariant `μ` is generic
  for a shift-invariant probability measure `Q_x`.
* `exists_isGenericPoint_upperOrbitComplexity_le` (proved from it and Proposition 7.10(i)):
  `K̄^{A'}(x, σ) ≤ h_{Q_x}(σ)` for every oracle `A'` computing the symbols of the ideal points.
* `RandomPointsInErgodicComponents` (a `def … : Prop`, not asserted) is Hoyrup's conclusion:
  every `μ`-random `x` is generic for an ergodic `Q_x` and `Q_x`-random relative to an oracle
  computing `Q_x`. Hoyrup proves it for effectively decomposable `μ` (and the other cases of
  the second bullet); whether it always holds is the open question of [HoyE] (third bullet).
  `localEntropy_eq_shiftEntropy_of_randomPointsInErgodicComponents` proves the conditional
  consequence: both orbit complexities and both local entropies of `μ` at `x` equal
  `h_{Q_x}(σ)` (Proposition 7.10(ii) and Theorem 3.3), the every-point form of Theorem 7.5(b)
  on shifts. A `def` was chosen over leaving the question unstated so that this consequence
  could be stated and proved; the question itself is never assumed outside that hypothesis.

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
  Mathlib or in this library. Only their conclusion (`RandomPointsInErgodicComponents`) and its
  consequence are stated.
* Remark 7.11: the translation of randomness for a non-computable measure into randomness
  relative to an oracle computing it (Reimann–Slaman; equivalent to uniform-test randomness
  by Day–Miller) is granted by the paper; here randomness for `Q_x` is always relative to an
  explicit admissible oracle `C`, which is the form the paper uses.
* The identification of the mean of `Λ_μ` in Remark 6.7 with the Kolmogorov–Sinai entropy
  `h_μ(T)`: Mathlib has no Kolmogorov–Sinai entropy (on shifts `shiftEntropy` of
  `ShiftGeneric.lean` would serve; the identification `h̲_μ(σ) = shiftEntropy μ` for ergodic
  `μ` is the Shannon–McMillan–Breiman theorem). The Feng–Huang entropy stands for `h_μ(T)`.
* The first two sentences of Remark 3.4 are commentary on Theorem 3.3, whose two halves are
  `orbitComplexityAt_le_localEntropyAt` (every point, every measure the oracle computes) and
  `localEntropyAt_le_orbitComplexityAt` (random points).

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

/-- The orbit complexity depends on the order and the radius only through the Bowen ball. -/
private lemma orbitComplexityNat_congr_ball {X : Type*} [MetricSpace X] (P : Presentation X)
    (T : X → X) (A : Set ℕ) (x : X) {n n' : ℕ} {r r' : ℝ}
    (h : bowenBall T n x r = bowenBall T n' x r') :
    orbitComplexityNat P T A x n r = orbitComplexityNat P T A x n' r' := by
  simp only [orbitComplexityNat, orbitComplexity, h]

/-! ### Remark 3.4 on Cantor space -/

section cantor

attribute [local instance] cantorMetricSpace

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

Proved in `Ergodic/CantorLevinSchnorr.lean` (`oracleComplexity_cantorPrefix_le_infoBits'`):
the cylinder coding theorem without change of scale. `w ↦ μ[w]` is `A`-lower semicomputable
(the cylinders are uniformly `A`-c.e. open by `hP`), and `oracle_coding_finite_mass`
(`Oracle/KraftChaitin.lean`) is applied to the words `w` with `μ[w] ≠ 0` at cost
`k₀(w) + 2(⌊log₂ |w|⌋ + 1)`, `k₀(w)` the least `k` with `2^{-k} < μ[w]`; the total weight is
finite because cylinders of the same length are disjoint.
Blueprint node `meas:remarks`. -/
theorem oracleComplexity_cantorPrefix_le_infoBits (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P shiftMap μ A) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n → μ (PiNat.cylinder x n) ≠ 0 →
      (oracleComplexity A (cantorPrefix x n) : ℝ) ≤
        (infoBits (μ (PiNat.cylinder x n))).toReal + c * Real.logb 2 n + c :=
  oracleComplexity_cantorPrefix_le_infoBits' P A hP μ hμ hA

/-- Remark 3.4(b), incompressibility direction of the Levin–Schnorr estimate with the
complexity of the word itself: if `A` is admissible for a probability measure `μ` and computes
the symbols of the ideal points, then at every `x ∈ R_A^μ`,
`-log₂ μ[x↾n] ≤ K^A(x↾n) + O(log n)` (in fact `+ O(1)` holds, Levin–Schnorr–Chaitin; the paper
states `O(log n)`).

Added hypothesis: `hP`, as in `oracleComplexity_cantorPrefix_le_infoBits`.

Proved in `Ergodic/CantorLevinSchnorr.lean`
(`infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints'`), with `+ O(1)` in fact: the
point is word-random (`mem_wordRandomPoints_of_mem_randomPoints`), the measure is
word-computable (`isComputableWordMeasureIn_of_isComputableMeasureIn`), and the word-level
Levin–Schnorr bound `exists_infoBits_le_wordComplexity_add` of `Ergodic/HoyrupBasic.lean`
applies.
Blueprint node `meas:remarks`. -/
theorem infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints
    (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P shiftMap μ A)
    {x : ℕ → Bool} (hx : x ∈ randomPoints P A μ) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      (infoBits (μ (PiNat.cylinder x n))).toReal ≤
        oracleComplexity A (cantorPrefix x n) + c * Real.logb 2 n + c :=
  infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints' P A hP μ hA hx

/-- Remark 3.4: on Cantor space, at every `μ`-random point relative to an admissible oracle `A`
that computes the symbols of the ideal points, the Levin–Schnorr estimate
`K^A(x↾n) = -log₂ μ[x↾n] + O(log n)` holds. Proved from the two directions
`oracleComplexity_cantorPrefix_le_infoBits` and
`infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints`.
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

/-- Remark 6.6 (and Proposition 6.12) on Cantor space, at the level of words: if `A` computes the
symbols of the ideal points, the information `-log₂ m^A[w]` of a cylinder under the universal
measure `m^A = ∑_i 2^{-K^A(i)} δ_{x_i}` is `K^A(w) + O(log |w|)`, for every word `w = x↾n`.

Proved in `Ergodic/UniversalMeasureWords.lean`
(`abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le'`): (1) the upper bound
`-log₂ m^A[w] ≤ K^A(w) + O(1)`, by an `A`-computable search for an ideal point `P.ι i_w ∈ [w]`
(`IsREIn.exists_computableIn_choice`, `P.dense`), `K^A(i_w) ≤ K^A(w) + O(1)` and
`m^A[w] ≥ 2^{-K^A(i_w)}`; (2) the lower bound `K^A(w) ≤ -log₂ m^A[w] + K^A(|w|) + O(1)` by
`oracle_coding_finite_mass`, since `w ↦ m^A[w]` is `A`-lower semicomputable and
`∑_w 2^{-k_w - K(|w|)} ≤ ∑_i 2^{-K^A(i)} ∑_n 2^{-K(n)} ≤ 1`; and `K^A(n) ≤ 3 log₂ n + O(1)`.
The change of scale of Proposition 6.12 is avoided by working with words.
Blueprint node `meas:remarks`. -/
theorem abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le
    (P : Presentation (ℕ → Bool)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ c : ℝ, ∀ (x : ℕ → Bool) (n : ℕ), 1 ≤ n →
      |(infoBits (universalMeasure P A (PiNat.cylinder x n))).toReal -
          oracleComplexity A (cantorPrefix x n)| ≤ c * Real.logb 2 n + c :=
  abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le' P A hP

/-- `(c log₂ n + c) / n → 0`. -/
private lemma tendsto_log_add_div (c : ℝ) :
    Tendsto (fun n : ℕ ↦ (c * Real.logb 2 n + c) / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ ↦ Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := ((h1.comp tendsto_natCast_atTop_atTop).const_mul (c / Real.log 2)).add
    (tendsto_one_div_atTop_nhds_zero_nat.const_mul c)
  simp only [mul_zero, add_zero] at h2
  refine h2.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hl : Real.log 2 ≠ 0 := by positivity
  simp only [Function.comp_apply, Real.logb]
  field_simp

/-- Two sequences of informations that differ by at most `c log₂ n + c` have the same lower and
upper growth rates. -/
private lemma rates_eq_of_le_add_log {a b : ℕ → ℝ≥0∞} (c : ℝ)
    (hab : ∀ᶠ n in atTop, a n ≤ b n + ENNReal.ofReal (c * Real.logb 2 n + c))
    (hba : ∀ᶠ n in atTop, b n ≤ a n + ENNReal.ofReal (c * Real.logb 2 n + c)) :
    (liminf (fun n : ℕ ↦ a n / n) atTop, limsup (fun n : ℕ ↦ a n / n) atTop) =
      (liminf (fun n : ℕ ↦ b n / n) atTop, limsup (fun n : ℕ ↦ b n / n) atTop) := by
  have hd : Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((c * Real.logb 2 n + c) / n)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_log_add_div c)
  have key : ∀ {u v : ℕ → ℝ≥0∞},
      (∀ᶠ n in atTop, u n ≤ v n + ENNReal.ofReal (c * Real.logb 2 n + c)) →
      ∀ᶠ n in atTop, u n / n ≤ v n / n + ENNReal.ofReal ((c * Real.logb 2 n + c) / n) := by
    intro u v h
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
    have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
    calc u n / n ≤ (v n + ENNReal.ofReal (c * Real.logb 2 n + c)) / n :=
          ENNReal.div_le_div_right hn _
      _ = _ := by rw [ENNReal.add_div, ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast]
  exact Prod.ext (le_antisymm (liminf_le_liminf_of_le_add_tendsto_zero (key hab) hd)
      (liminf_le_liminf_of_le_add_tendsto_zero (key hba) hd))
    (le_antisymm (limsup_le_limsup_of_le_add_tendsto_zero (key hab) hd)
      (limsup_le_limsup_of_le_add_tendsto_zero (key hba) hd))

/-- Remark 6.6 for the empty oracle, second sentence: `Ψ^∅` is the pair of local entropies of
the a priori probability `M`, that is, at every point `x` of Cantor space
`K̲(x, σ) = liminf_n KA(x↾n) / n` and `K̄(x, σ) = limsup_n KA(x↾n) / n`, with
`KA(w) = -log₂ M(w)` (`Kolmogorov.KA`).

Divergences from the paper: only the empty oracle and the binary alphabet (see
`abs_oracleComplexity_empty_sub_KA_le`); added hypotheses: the presentation is computable, the
shift is represented, and the symbols of the ideal points are computable (the standard
computable presentation of Cantor space, which the paper leaves implicit). The local entropies
of `M` are expressed by the growth rates of `KA`, since `M` is a semimeasure on words, not a
measure on the space. Proved from Proposition 6.12
(`orbitComplexities_eq_localEntropy_universalMeasure`), the cylinder formula
`localEntropy_shiftMap`, the comparison
`abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le` and
`abs_oracleComplexity_empty_sub_KA_le`. Blueprint node `meas:remarks`. -/
theorem orbitComplexities_eq_rates_KA (P : Presentation (ℕ → Bool))
    (hPc : ComputablePresentationIn P ∅) (hT : IsRepresentedMapIn P P ∅ shiftMap)
    (hP : ComputableIn {charOracle ∅} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) (x : ℕ → Bool) :
    orbitComplexities P shiftMap ∅ x =
      (liminf (fun n : ℕ ↦ ENNReal.ofReal (KA (cantorPrefix x n)) / n) atTop,
        limsup (fun n : ℕ ↦ ENNReal.ofReal (KA (cantorPrefix x n)) / n) atTop) := by
  rw [orbitComplexities_eq_localEntropy_universalMeasure P shiftMap continuous_shiftMap_cantor ∅
    hPc hT x, localEntropy_shiftMap (β := 1 / 2) (by norm_num) (by norm_num) cantor_hd]
  obtain ⟨c₁, h₁⟩ := abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le P ∅ hP
  obtain ⟨c₂, h₂⟩ := abs_oracleComplexity_empty_sub_KA_le
  set c : ℝ := |c₁| + 2 + |c₂|
  have hreal : ∀ n : ℕ, 1 ≤ n →
      |(infoBits (universalMeasure P ∅ (PiNat.cylinder x n))).toReal - KA (cantorPrefix x n)| ≤
        c * Real.logb 2 n + c := by
    intro n hn
    have e₁ := h₁ x n hn
    have e₂ := h₂ (cantorPrefix x n)
    rw [cantorPrefix_length] at e₂
    have hl := logb_natCast_nonneg n
    have k₁ : c₁ * Real.logb 2 n ≤ |c₁| * Real.logb 2 n :=
      mul_le_mul_of_nonneg_right (le_abs_self c₁) hl
    have k₂ : c * Real.logb 2 n = |c₁| * Real.logb 2 n + 2 * Real.logb 2 n +
        |c₂| * Real.logb 2 n := by ring
    have k₃ : 0 ≤ |c₂| * Real.logb 2 n := mul_nonneg (abs_nonneg _) hl
    unfold KA
    rw [abs_le] at e₁ e₂ ⊢
    constructor <;> linarith [le_abs_self c₁, le_abs_self c₂, neg_abs_le c₁]
  have hne : ∀ n : ℕ, 1 ≤ n → infoBits (universalMeasure P ∅ (PiNat.cylinder x n)) ≠ ⊤ := by
    intro n hn
    have h := universalMeasure_bowenBall_ge P shiftMap continuous_shiftMap_cantor ∅ x hn
      one_pos
    rw [bowenBall_shiftMap_one_cantor x hn] at h
    have h0 : universalMeasure P ∅ (PiNat.cylinder x n) ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp)) _) h).ne'
    rw [infoBits_of_ne h0]
    exact ENNReal.ofReal_ne_top
  refine rates_eq_of_le_add_log c ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  · have e := (abs_le.1 (hreal n hn)).2
    rw [← ENNReal.ofReal_toReal (hne n hn)]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_add_le
  · have e := (abs_le.1 (hreal n hn)).1
    rw [← ENNReal.ofReal_toReal (hne n hn)]
    exact (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_add_le

end cantor

/-! ### Remark 6.7: invariant measures -/

section invariant

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

omit [SecondCountableTopology X] in
/-- Remark 6.7, the Brin–Katok formula, first half (Brin–Katok [BK], Theorem 1): on a compact
space, for a continuous `T` and a `T`-invariant probability measure `μ`, the lower and upper
local entropies agree `μ`-almost everywhere.

Proved from the ergodic decomposition (`Kolmogorov.Ergodic.exists_ergodicDecomposition`) and
Theorem 7.5(b) (`ae_localEntropy_fst_eq_snd_of_invariant` in
`Measure/Ergodic/BrinKatokNonErgodic.lean`): both local entropies equal the Kolmogorov–Sinai
entropy of the ergodic component. The finiteness hypothesis `h̄_μ(T) < ∞` of the first
formalization is not needed and has been dropped. Blueprint node `meas:remarks`. -/
theorem ae_localEntropy_fst_eq_snd_of_measurePreserving [CompactSpace X] {T : X → X}
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, (localEntropy μ T x).1 = (localEntropy μ T x).2 :=
  ae_localEntropy_fst_eq_snd_of_invariant hT μ hμ

omit [SecondCountableTopology X] in
/-- Remark 6.7, the Brin–Katok formula for an ergodic measure: on a compact space, for a
continuous `T` and an ergodic `T`-invariant probability measure `μ`, the local entropy is
almost everywhere the constant `(h, h)`, where `h = h̲_μ(T)` is the lower Feng–Huang entropy.

Proved from Theorem 1 of the note *Orbit complexity of Martin-Löf random points equals entropy*
(`ae_localEntropy_eq_measureEntropy_of_ergodic` in `Measure/Ergodic/OrbitEntropy.lean`): both
local entropies equal the Kolmogorov–Sinai entropy `h_μ(T)` (`Ergodic.ksEntropy`) almost
everywhere, and so do both Feng–Huang entropies (`measureEntropy_eq_ksEntropy`). That theorem
is fully proved, Hoyrup's theorem included (`shiftEntropy_le_liminf_wordComplexity_bool`).
The finiteness hypothesis `h̄_μ(T) < ∞` of the first formalization is not needed and has been
dropped. Blueprint node `meas:remarks`. -/
theorem ae_localEntropy_eq_of_ergodic [CompactSpace X] {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : Ergodic T μ) :
    ∀ᵐ x ∂μ, localEntropy μ T x = ((measureEntropy μ T).1, (measureEntropy μ T).1) :=
  ae_localEntropy_eq_measureEntropy_of_ergodic hT μ hμ

omit [SecondCountableTopology X] in
/-- Remark 6.7: for a `T`-invariant probability measure on a compact space,
the entropy law `Λ_μ` is carried by the diagonal. Proved from the Brin–Katok statement
`ae_localEntropy_fst_eq_snd_of_measurePreserving`. Blueprint node `meas:remarks`. -/
theorem ae_entropyLaw_fst_eq_snd [CompactSpace X] {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : MeasurePreserving T μ μ) :
    ∀ᵐ p ∂entropyLaw μ T, p.1 = p.2 := by
  rw [entropyLaw, ae_map_iff (measurable_localEntropy μ hT).aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd)]
  exact ae_localEntropy_fst_eq_snd_of_measurePreserving hT μ hμ

omit [SecondCountableTopology X] in
/-- Remark 6.7: for a `T`-invariant probability measure on a compact space,
the two marginals of `Λ_μ` have the same mean: `h̲_μ(T) = h̄_μ(T)` (the mean of `Λ_μ` on the
diagonal, which Brin–Katok identifies with `h_μ(T)`). Proved from
`ae_localEntropy_fst_eq_snd_of_measurePreserving`. The identification of this common mean with
the Kolmogorov–Sinai entropy is `jacobs_lintegral_entropyLaw_fst` and
`jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving` (`Ergodic/KSInvariant.lean`, via
Jacobs' theorem). Blueprint node `meas:remarks`. -/
theorem measureEntropy_fst_eq_snd_of_measurePreserving [CompactSpace X] {T : X → X}
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving T μ μ) :
    (measureEntropy μ T).1 = (measureEntropy μ T).2 :=
  lintegral_congr_ae (ae_localEntropy_fst_eq_snd_of_measurePreserving hT μ hμ)

omit [SecondCountableTopology X] in
/-- Remark 6.7: for an ergodic measure on a compact space the entropy law is the point mass
`δ_{(h, h)}`, `h = h̲_μ(T)`. Proved from `ae_localEntropy_eq_of_ergodic`.
Blueprint node `meas:remarks`. -/
theorem entropyLaw_eq_dirac_of_ergodic [CompactSpace X] {T : X → X} (hT : Continuous T)
    (μ : Measure X) [IsProbabilityMeasure μ] (hμ : Ergodic T μ) :
    entropyLaw μ T = Measure.dirac ((measureEntropy μ T).1, (measureEntropy μ T).1) := by
  rw [entropyLaw, Measure.map_congr (ae_localEntropy_eq_of_ergodic hT μ hμ),
    Measure.map_const, measure_univ, one_smul]

/-- Remark 6.7, countably many ergodic components: if `μ = ∑_j t_j μ_j` with all `t_j > 0`,
every `μ_j` an ergodic `T`-invariant probability measure, on a compact space,
then `Λ_μ = ∑_j t_j δ_{(h_j, h_j)}` with `h_j = h̲_{μ_j}(T)` (which stands for `h_{μ_j}(T)`).

Divergences from the paper: `h_j` is the Feng–Huang entropy (see
`ae_localEntropy_eq_of_ergodic`); the weights need not sum to one, and no finiteness of the
entropy is needed. Proved from
Proposition 6.3 (`entropyLaw_sum`) and the ergodic Brin–Katok statement
`ae_localEntropy_eq_of_ergodic`. Blueprint node `meas:remarks`. -/
theorem entropyLaw_sum_ergodic [CompactSpace X] {T : X → X} (hT : Continuous T) {ι : Type*}
    [Countable ι] (t : ι → ℝ≥0∞) (μs : ι → Measure X) [∀ j, IsProbabilityMeasure (μs j)]
    [IsFiniteMeasure (Measure.sum fun j ↦ t j • μs j)] (ht : ∀ j, t j ≠ 0)
    (herg : ∀ j, Ergodic T (μs j)) :
    entropyLaw (Measure.sum fun j ↦ t j • μs j) T =
      Measure.sum fun j ↦
        t j • Measure.dirac ((measureEntropy (μs j) T).1, (measureEntropy (μs j) T).1) := by
  rw [entropyLaw_sum hT t μs ht]
  congr 1
  funext j
  rw [entropyLaw_eq_dirac_of_ergodic hT (μs j) (herg j)]

omit [SecondCountableTopology X] in
/-- Remark 6.7, last sentence: in general `Λ_μ` is the distribution of the entropy of the
ergodic component. For an ergodic decomposition `μ = ∫ μ_ω dQ(ω)` given by a Markov kernel `κ`
(a `T`-invariant `μ` on a compact space, `μ_ω` ergodic for `Q`-almost every `ω`), `Λ_μ` is the
law of `(h_{μ_ω}, h_{μ_ω})` under `M = Q ⊗ κ`, `h_{μ_ω} = h̲_{μ_ω}(T)`.
Proved from Theorem 7.5(b) (`ae_compProd_localEntropy_eq_of_ergodicDecomposition`).

Divergence from the paper: the law is taken under `M`, the joint law of the component and the
point, rather than under `Q`; this avoids a measurability hypothesis on `ω ↦ h_{μ_ω}`.
Blueprint node `meas:remarks`. -/
theorem entropyLaw_eq_map_of_ergodicDecomposition [CompactSpace X] {T : X → X}
    (hT : Continuous T) {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (κ : Kernel Ω X) [IsMarkovKernel κ] (hinv : MeasurePreserving T (Q.bind κ) (Q.bind κ))
    (herg : ∀ᵐ ω ∂Q, Ergodic T (κ ω)) :
    entropyLaw (Q.bind κ) T = Measure.map (fun p : Ω × X ↦
      ((measureEntropy (κ p.1) T).1, (measureEntropy (κ p.1) T).1)) (Q ⊗ₘ κ) := by
  have h := ae_compProd_localEntropy_eq_of_ergodicDecomposition hT Q κ hinv herg
  refine Eq.trans ?_ (Measure.map_congr (h.mono fun p hp ↦ hp.1))
  rw [entropyLaw, ← Measure.snd_compProd Q κ, Measure.snd,
    Measure.map_map (measurable_localEntropy _ hT) measurable_snd]
  rfl

end invariant

/-! ### Remark 7.11: generic points of random points -/

section generic

variable {α : Type*} [Fintype α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
  [BorelSpace (ℕ → α)] [Primcodable α] {β : ℝ}

omit [Fintype α] in
/-- Remark 7.11, first bullet, the input: V'yugin's effective ergodic theorem [Vyu], relativized.
If `μ` is a shift-invariant probability measure, `A` is admissible for `μ` and computes the
symbols of the ideal points, then every `μ`-random point `x` relative to `A` is generic for some
shift-invariant probability measure `Q_x` (the frequencies of all words in `x` converge).

Added hypothesis (as in `upperOrbitComplexity_le_shiftEntropy`): `hP`, which makes the cylinders
effectively clopen in the presentation, so that their indicators are `A`-computable functions.
The paper takes `μ` computable and randomness without oracle; here everything is relative to
`A`.

Proved (`exists_isGenericPoint_of_mem_randomPoints'` in `Ergodic/VyuginGenericity.lean`), by
V'yugin's route (V. V. V'yugin, *Ergodic theorems for individual random sequences*, 1997;
relativized): Bishop's upcrossing inequality (`Ergodic/Upcrossing.lean`) turns the set of points
whose frequency of a word oscillates `k` times across `[a, b]` into a `μ`-test, so the
frequencies of all words converge at every random point (`Ergodic/VyuginFrequencies.lean`); the
limits define a shift-invariant probability measure for which `x` is generic (a cluster point of
the empirical measures). The computability of `μ` is not used.
Blueprint node `meas:remarks`. -/
theorem exists_isGenericPoint_of_mem_randomPoints [Finite α] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → α)) [IsProbabilityMeasure μ] (hμ : MeasurePreserving shiftMap μ μ)
    (hA : IsMeasureAdmissible P shiftMap μ A) {x : ℕ → α} (hx : x ∈ randomPoints P A μ) :
    ∃ ν : Measure (ℕ → α), IsProbabilityMeasure ν ∧ MeasurePreserving shiftMap ν ν ∧
      IsGenericPoint ν x :=
  exists_isGenericPoint_of_mem_randomPoints' hβ hβ₁ hd P A hP μ hμ hA hx

/-- Remark 7.11, first bullet: "half of the statement is unconditional", `K̄(x, σ) ≤ h_{Q_x}(σ)`.
Under the hypotheses of `exists_isGenericPoint_of_mem_randomPoints`, a `μ`-random point `x` is
generic for a shift-invariant probability measure `Q_x`, and for every oracle `A'` computing the
symbols of the ideal points (for instance `A' = ∅` for the standard presentation)
`K̄^{A'}(x, σ) ≤ h_{Q_x}(σ)` (`shiftEntropy`).

Proved from `exists_isGenericPoint_of_mem_randomPoints` (V'yugin) and Proposition 7.10(i)
(`upperOrbitComplexity_le_shiftEntropy`, in `Ergodic/Proposition710.lean`).
Blueprint node `meas:remarks`. -/
theorem exists_isGenericPoint_upperOrbitComplexity_le (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → α)) [IsProbabilityMeasure μ] (hμ : MeasurePreserving shiftMap μ μ)
    (hA : IsMeasureAdmissible P shiftMap μ A) {x : ℕ → α} (hx : x ∈ randomPoints P A μ) :
    ∃ ν : Measure (ℕ → α), IsProbabilityMeasure ν ∧ MeasurePreserving shiftMap ν ν ∧
      IsGenericPoint ν x ∧ ∀ A' : Set ℕ,
        ComputableIn {charOracle A'} (fun q : ℕ × ℕ ↦ P.ι q.1 q.2) →
          (orbitComplexities P shiftMap A' x).2 ≤ shiftEntropy ν := by
  obtain ⟨ν, hν, hνinv, hgen⟩ :=
    exists_isGenericPoint_of_mem_randomPoints hβ hβ₁ hd P A hP μ hμ hA hx
  exact ⟨ν, hν, hνinv, hgen, fun A' hP' ↦
    upperOrbitComplexity_le_shiftEntropy hβ hβ₁ hd P A' hP' ν hνinv hgen⟩

/-- Remark 7.11, the conclusion of Hoyrup's theorems and the open question of [HoyE], as a
proposition (NOT asserted): every `μ`-random point `x` relative to `A` is generic for an ergodic
shift-invariant probability measure `Q_x` (its ergodic component) and is `Q_x`-random relative
to some oracle `C ≥_T A` admissible for `Q_x`.

Hoyrup (M. Hoyrup, *Computability of the ergodic decomposition*, [HoyE]) proves this (for
`A = ∅`) when `μ` is computable and effectively decomposable, when the representing measure of
the ergodic decomposition is carried by a closed set of ergodic measures, and for V'yugin's
non-effectively decomposable example; whether it holds for every computable shift-invariant
`μ` is open. Randomness for the non-computable `Q_x` is expressed through an oracle computing
it (the translation the paper grants). Recorded as a `def … : Prop` so that its consequence can
be proved (`localEntropy_eq_shiftEntropy_of_randomPointsInErgodicComponents`); the
effective-decomposability statements themselves are under `Not stated`.
Blueprint node `meas:remarks`. -/
def RandomPointsInErgodicComponents (P : Presentation (ℕ → α)) (A : Set ℕ)
    (μ : Measure (ℕ → α)) : Prop :=
  ∀ x ∈ randomPoints P A μ, ∃ ν : Measure (ℕ → α), IsProbabilityMeasure ν ∧
    IsGenericPoint ν x ∧ Ergodic shiftMap ν ∧ ∃ C : Set ℕ,
      IsMeasureAdmissible P shiftMap ν C ∧ charOracle A ≤ᵀ charOracle C ∧
        x ∈ randomPoints P C ν

/-- Remark 7.11, second and third bullets: the consequence of `RandomPointsInErgodicComponents`
(Hoyrup's conclusion, proved by him for effectively decomposable `μ`, open in general). If it
holds for `μ` and `A` (admissible for `μ`, computing the symbols of the ideal points), then at
every `μ`-random point `x` relative to `A`, with `Q_x` its ergodic generic measure,
`K̲^A(x, σ) = K̄^A(x, σ) = h_{Q_x}(σ)` (Proposition 7.10(ii)), and the local entropies of `μ`
at `x` both equal `h_{Q_x}(σ)` (Theorem 3.3): the every-point form of Theorem 7.5(b) on shifts.
For `A = ∅` this is `K(x↾n)/n → h_{Q_x}(σ)`.

Proved from Proposition 7.10(ii) (`orbitComplexities_eq_shiftEntropy`, in
`Ergodic/Proposition710.lean`) and `orbitComplexities_eq_localEntropy`.
Blueprint node `meas:remarks`. -/
theorem localEntropy_eq_shiftEntropy_of_randomPointsInErgodicComponents (hβ : 0 < β)
    (hβ₁ : β < 1) (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2)
    (μ : Measure (ℕ → α)) [IsProbabilityMeasure μ] (hA : IsMeasureAdmissible P shiftMap μ A)
    (h : RandomPointsInErgodicComponents P A μ) {x : ℕ → α} (hx : x ∈ randomPoints P A μ) :
    ∃ ν : Measure (ℕ → α), IsProbabilityMeasure ν ∧ IsGenericPoint ν x ∧
      Ergodic shiftMap ν ∧
      orbitComplexities P shiftMap A x = (shiftEntropy ν, shiftEntropy ν) ∧
      localEntropy μ shiftMap x = (shiftEntropy ν, shiftEntropy ν) := by
  obtain ⟨ν, hν, hgen, herg, C, hC, hAC, hxC⟩ := h x hx
  have hΨ := orbitComplexities_eq_shiftEntropy hβ hβ₁ hd P ν herg hC hxC hAC hP
  refine ⟨ν, hν, hgen, herg, hΨ, ?_⟩
  rw [← orbitComplexities_eq_localEntropy P shiftMap (continuous_shiftMap hβ hβ₁ hd) A μ hA hx,
    hΨ]

end generic

end Kolmogorov.PointToSet
