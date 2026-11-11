# Entropy of non-invariant measures: blueprint and its Lean formalization

This file maps the statements of the working note *Entropy of non-invariant measures and orbit
complexity of random points* (Emma Dinowitz, 10 November 2026; statements with proof sketches)
to the Lean declarations that formalize them. The Lean docstrings carry the same references
(search for `Blueprint node \`meas:` in `KolmogorovMathlib/PointToSet/Measure`).

The note says of itself that its proofs are sketches that have not been checked. The
formalization was done in two passes. The first covers the core: the setting of §2.2–2.3, the
pointwise theorem of §3, the universal measure and the dual principle of §6.3, and the
domination lemma of §7.2 with its classical consequences (sections 1–4 below). The second
covers the rest of the note: §4, the remaining parts of §6 and §7, §8 and the examples
(sections 5–10 below). What is stated but not proved is listed under "Open leaves"; what is
not stated at all under "Not stated".

## Conventions

* Paths are relative to `KolmogorovMathlib/`; every declaration lives in the namespace
  `Kolmogorov.PointToSet`. The new chapter is `PointToSet/Measure/`.
* The space is a metric space `X` with a `Presentation P` (a fixed dense sequence of ideal
  points `P.ι i`, completeness), a Borel σ-algebra, and a continuous map `T`. Oracles are sets
  `A : Set ℕ`; `K^A(i)` is `oracleNatComplexity A i`, `K_n^A(x, T, ε)` is
  `orbitComplexityNat P T A x n ε`, and `(K̲^A(x, T), K̄^A(x, T))` is the pair
  `orbitComplexities P T A x` of the point-to-set chapter.
* **Values.** Local entropies and orbit complexities take values in `ℝ≥0∞`. The information
  `-log₂ q` of a mass `q` is `infoBits q`, infinite at `q = 0` and truncated at `0` for
  `q > 1`, so the definitions are total for arbitrary measures; for measures of total mass at
  most one there is no truncation.
* **Scales.** As in the rest of `PointToSet/`, limits `ε → 0` are suprema over the dyadic
  radii `dyadicRadius p = 2^{-p}`. Statements at a fixed scale take a real or rational `ε`;
  the pairs `localEntropyAt μ T x ε` and `orbitComplexityAt P T A x ε` are the lower and upper
  rates at the scale `ε`. Pairs `(lower, upper)` are selected by `.1` / `.2`.
* **Measures.** `μ` is `A`-computable (`IsComputableMeasureIn P A μ`) when the measures of
  finite unions of basic balls with rational radii (`ballUnion P L`) are lower semicomputable
  in `A`, uniformly in the list `L`. `A` is admissible for `(X, d, T, μ)`
  (`IsMeasureAdmissible P T μ A`) when it computes the metric table, represents `T` and
  computes `μ`.
* **Randomness.** A `μ`-test relative to `A` is a uniformly `A`-c.e. open sequence `(U_m)`
  with `μ(U_m) ≤ 2^{-m}` (`IsMeasureTestIn`); `randomPoints P A μ` is the set `R_A^μ`.
* Marks: **✎** the statement is corrected or repaired with respect to the printed claim;
  **◇** the node is realized by a different but equivalent or sufficient statement.

## Main theorems

* **Theorem 3.3** (orbit complexity of random points):
  `Kolmogorov.PointToSet.orbitComplexities_le_localEntropy` (every point) and
  `Kolmogorov.PointToSet.orbitComplexities_eq_localEntropy` (every random point), in
  `PointToSet/Measure/Pointwise.lean`.
* **Corollary 3.6** (Billingsley-type bounds): `lowerEntropy_le_of_localEntropy_le`,
  `upperEntropy_le_of_localEntropy_le`, `le_lowerEntropy_of_le_localEntropy`,
  `le_upperEntropy_of_le_localEntropy` (`PointToSet/Measure/Pointwise.lean`).
* **Proposition 6.12** (universal measure):
  `orbitComplexities_eq_localEntropy_universalMeasure`
  (`PointToSet/Measure/UniversalMeasure.lean`).
* **Corollary 6.14** (dual principle): `lowerEntropy_eq_iInf_measure`,
  `upperEntropy_eq_iInf_measure` (`PointToSet/Measure/UniversalMeasure.lean`).
* **Lemma 7.1** (domination): `ae_eventually_measure_bowenBall_le`
  (`PointToSet/Measure/Domination.lean`).
* **Theorem 7.3** (integral decompositions): `ae_compProd_localEntropy_le`,
  `kernelEntropyLaw_eq_iff`, `lintegral_measureEntropy_le`
  (`PointToSet/Measure/Decomposition.lean`).

## Status (11 November 2026)

The chapter is 31 modules, about 14,100 lines, 625 public declarations, all with docstrings.
`lake build` of the 31 modules succeeds; the only warnings are the 7 `sorry`s listed under
"Open leaves". `#print axioms` on all 625 public declarations: 607 depend only on `propext`,
`Classical.choice` and `Quot.sound`; the other 18 are the 7 open leaves and the 11 statements
derived from them.

## 1. Setting (§2)

Files: `PointToSet/Measure/LocalEntropy.lean`, `BowenCeOpen.lean`, `Computable.lean`,
`Randomness.lean`.

* **`meas:info`** — the information `-log₂ q ∈ [0, ∞]` of a mass.
  `infoBits` (`LocalEntropy.lean`); same file: `infoBits_zero`, `_top`, `_of_ne`, `_ofReal`,
  `_lt_top`, `_eq_top_iff`, `_antitone`, `two_inv_pow_lt_of_infoBits_lt`,
  `infoBits_le_of_rpow_le`, `le_infoBits_of_le_rpow`, `infoBits_le_infoBits_mul_add`,
  `infoBits_mul_le`.
* **`meas:local-entropy`** (§2.3) — closed Bowen balls and local entropies
  `h̲_μ(T, x, ε)`, `h̄_μ(T, x, ε)`, `h̲_μ(T, x)`, `h̄_μ(T, x)`; monotonicity in the scale;
  invariance under rescaling the measure; measurability.
  `closedBowenBall`, `localEntropyRate`, `localEntropyAt`, `localEntropy`, `orbitComplexityAt`
  (`LocalEntropy.lean`); same file: `mem_closedBowenBall_iff`,
  `bowenBall_subset_closedBowenBall`, `closedBowenBall_subset_bowenBall`,
  `isClosed_closedBowenBall`, `bowenBall_subset_bowenBall_add`,
  `closedBowenBall_subset_bowenBall_two_mul`, `orbitComplexities_eq_iSup_orbitComplexityAt`,
  `orbitComplexityAt_antitone`, `orbitComplexityAt_le_orbitComplexities`,
  `localEntropyRate_antitone`, `localEntropyAt_antitone`, `localEntropyAt_fst_le_snd`,
  `localEntropy_fst_le_snd`, `localEntropyAt_le_localEntropy`, `localEntropy_le_of_forall_rat`,
  `localEntropyAt_smul`, `localEntropy_smul`, `measurable_measure_bowenBall` (the mass of a
  Bowen ball is lower semicontinuous in its centre), `measurable_localEntropyRate`,
  `measurable_localEntropyAt`, `measurable_localEntropy`; the sequence lemmas
  `liminf_le_liminf_of_le_add_tendsto_zero`, `limsup_le_limsup_of_le_add_tendsto_zero`.
* **`meas:entropy-law`** (§4.1, Definition 6.1) — the Feng–Huang entropies as integrals of
  the local entropies and the entropy law `Λ_μ = (Φ_μ)_* μ`.  ◇ `Λ_μ` is a measure on
  `ℝ≥0∞ × ℝ≥0∞`; the triangle `Δ = {s ≤ t}` is not introduced
  (`localEntropy_fst_le_snd` says the law is carried by it).
  `measureEntropy`, `entropyLaw` (`LocalEntropy.lean`).
* **`meas:bowen-ce-open`** (§2.2, (M2)) — Bowen balls about ideal points with rational radii
  are `A`-effectively open, and closed Bowen balls `A`-effectively closed, uniformly in
  `(n, i, ε)`, for `A` computing the metric table and representing `T`.
  `isCeOpenFamilyIn_bowenBall`, `isCeOpenFamilyIn_compl_closedBowenBall`
  (`BowenCeOpen.lean`); same file: the refined representation `bowenChainRep`,
  `exists_bowenChainRep`, and the general theorem `isCeOpenFamilyIn_bowenChainSet` on sets cut
  out by chains of basic balls (`bowenChainSet`, `bowenChain_iterate_mem`,
  `bowenChain_exists_chain`).
* **`meas:computable`** (§2.2, (M1)) — `A`-computable measures; every measure is
  `A`-computable on an upper cone; `μ(U)` is lower semicomputable for `A`-effectively open `U`
  and, for a probability measure, `μ(F)` is upper semicomputable for `A`-effectively closed
  `F`, uniformly.
  `IsComputableMeasureIn` (`Computable.lean`); same file: `IsComputableMeasureIn.mono_oracle`,
  `exists_oracle_isComputableMeasureIn`, `IsComputableMeasureIn.lowerSemicomputable_ceOpen`,
  `IsComputableMeasureIn.isREIn_measure_compl_lt`.
* **`meas:admissible`** (§2.2) — oracles admissible for `(X, d, T, μ)` form an upper set
  containing a cone; the measures of open and closed Bowen balls about ideal points are lower
  and upper semicomputable.
  `IsMeasureAdmissible` (`Computable.lean`); same file: `IsMeasureAdmissible.mono_oracle`,
  `exists_measureAdmissible_base`, `IsMeasureAdmissible.lowerSemicomputable_bowenBall`,
  `IsMeasureAdmissible.isREIn_measure_closedBowenBall_lt`.
* **`meas:random`** (§2.2) — `μ`-tests, `R_A^μ`, `μ(R_A) = 1`, `R_B ⊆ R_A` for `B ≥_T A`.
  `IsMeasureTestIn`, `randomPoints` (`Randomness.lean`); same file:
  `IsMeasureTestIn.mono_oracle`, `randomPoints_anti_oracle`,
  `not_forall_mem_of_mem_randomPoints` (tests may be shifted by a constant factor),
  `countable_setOf_isREIn`, `measure_compl_randomPoints`, `ae_mem_randomPoints`,
  `exists_mem_randomPoints_of_measure_pos`.
  The closing remark of §2.2 (a lower semicomputable `t` with finite integral is finite on
  `R_A`) is not stated in general, since lower semicomputable functions on `X` are not
  defined; its instance for the test function of Lemma 3.2 is
  `testFunction_lt_top_of_mem_randomPoints` (see `meas:test`).

## 2. The pointwise theorem (§3)

Files: `PointToSet/Measure/CodingByMeasure.lean`, `DeficiencyTest.lean`, `Pointwise.lean`.

* **`meas:coding`** (Lemma 3.1, coding by measure) — for rational `ε > 0` there is `c` with
  `K_n^A(x, T, 6ε) ≤ I + 2 log₂ n + 2 log₂ (I + 2) + c`, `I = -log₂ μ(B_n(x, T, ε))`.
  The hypothesis on the measure is `μ(X) ≤ 1`, so the lemma also applies to `m^A`.
  `coding_by_measure_info` (`CodingByMeasure.lean`); `coding_by_measure` is the form used for
  limits, with any `k` such that `2^{-k} < μ(B_n(x, T, ε))` in place of `I + 1`. Same file:
  the greedy selection `greedyList`, `greedyEnum` and its invariants, `card_le_two_pow_of_far`,
  `exists_dec_far_near`, `exists_selection`, `exists_complexity_le_selCost`.
* **`meas:test`** (Lemma 3.2, a test) — ◇ ✎.
  * The test function `t_ε` is `testFunction`; `testFunction_pos` (`0 < t_ε`),
    `lintegral_testFunction_lt_two` (`∫ t_ε dμ < 2`).
  * ✎ The inequality
    `-log₂ μ(B_n(x, T, 2ε)) ≤ K_n^A(x, T, ε) + 2 log₂ n + log₂ t_ε(x)` is
    `testFunction_mul_measure_bowenBall_ge`, in the multiplicative form
    `2^{-K_n^A(x, T, ε)} n^{-2} ≤ t_ε(x) μ(B_n(x, T, 2ε))` and under the hypothesis
    `t_ε(x) < ∞`. In `ℝ≥0∞` the multiplicative form is false when `t_ε(x) = ∞` and the ball is
    null (`∞ · 0 = 0`); the additive form of the note is then the vacuous `∞ ≤ ∞`.
  * ◇ The use of randomness ("`t_ε < ∞` on `R_A`") is realized by a Martin-Löf test built
    from the single summands of `t_ε` instead of the sum: the levels
    `V_m = ⋃ {B_n(x_i, T, ε) : μ(B̄_n(x_i, T, ε)) < 2^{-K^A(i) - m} n^{-2}}`
    (`deficiencyLevel`) are uniformly `A`-c.e. open (`isCeOpenFamilyIn_deficiencyLevel`) with
    `μ(V_m) ≤ 2 · 2^{-m}` (`measure_deficiencyLevel_le`). A random point leaves some `V_m`
    (`exists_deficiency_bound`), which gives
    `-log₂ μ(B_n(x, T, 2ε)) ≤ K_n^A(x, T, ε) + 2 log₂ n + m` for a constant `m = m(x)`
    (`exists_measure_bowenBall_ge_of_mem_randomPoints`). This is what Theorem 3.3 uses.
  * The finiteness of the sum itself, `t_ε(x) < ∞` for `x ∈ R_A`, is
    `testFunction_lt_top_of_mem_randomPoints` (`TestFunctionFinite.lean`): the levels
    `{t_ε > 2^m}` are uniformly `A`-c.e. open (certified finite lists of Bowen balls, using
    `IsCeOpenFamilyIn.biInter_list`) and have measure at most `2 · 2^{-m}`. Lower
    semicomputability of `t_ε` as a notion for functions on `X` is not introduced.
  (`DeficiencyTest.lean`; helpers `tsum_inv_sq_lt_two`, `tsum_tsum_weight_le`,
  `IsCeOpenFamilyIn.iUnion_of_isREIn`.)
* **`meas:pointwise`** (Theorem 3.3, orbit complexity of random points) —
  (i) `orbitComplexityAt_le_localEntropyAt`: `K̲^A(x, T, 6ε) ≤ h̲_μ(T, x, ε)` and the same
  for the upper quantities, at every `x`;
  (ii) `localEntropyAt_le_orbitComplexityAt`: `h̲_μ(T, x, 2ε) ≤ K̲^A(x, T, ε)` and the same for
  the upper quantities, at every `x ∈ R_A`;
  consequently `orbitComplexities_le_localEntropy` (every point) and
  `orbitComplexities_eq_localEntropy` (every random point);
  `ae_orbitComplexities_eq_localEntropy` (`Pointwise.lean`).
  Part (i) needs only `μ(X) ≤ 1`; part (ii) a probability measure.
* **`meas:billingsley`** (Corollary 3.6) — (a) `lowerEntropy_le_of_localEntropy_le`,
  `upperEntropy_le_of_localEntropy_le`; (b) `le_lowerEntropy_of_le_localEntropy`,
  `le_upperEntropy_of_le_localEntropy`, where "positive outer measure" is `μ Z ≠ 0`
  (`Pointwise.lean`). `h̲(Z, T)` is `lowerEntropy T Z` and `h̄(Z, T)` is `upperEntropy P T Z`.

Remarks 3.4 and 3.5 are not formalized.

## 3. The universal measure and the dual principle (§6.3)

File: `PointToSet/Measure/UniversalMeasure.lean`.

* **`meas:universal`** (Definition 6.11, Proposition 6.12) — `m^A = ∑_i 2^{-K^A(i)} δ_{x_i}`
  has mass in `(0, 1]`, is carried by the ideal points, and is `A`-computable when `A`
  computes the metric table. `I ≤ K_n^A(x, T, ε)` and
  `K_n^A(x, T, 6ε) ≤ I + 2 log₂ n + 2 log₂ (I + 2) + c` with `I = -log₂ m^A(B_n(x, T, ε))`;
  consequently `Ψ^A(x) = Φ_{m^A}(x)` at every point.
  `universalMeasure`; `universalMeasure_apply`, `_univ_le_one`, `_univ_ne_zero`,
  `_compl_range`, `isComputableMeasureIn_universalMeasure`,
  `isMeasureAdmissible_universalMeasure`, `universalMeasure_bowenBall_ge` (first inequality,
  multiplicative form), `orbitComplexityNat_le_of_lt_universalMeasure` (second inequality, in
  the `k`-form of `coding_by_measure`), `orbitComplexities_eq_localEntropy_universalMeasure`.
* **`meas:dual`** (Corollary 6.14, dual principle) —
  `h̲(Z, T) = min_μ sup_{x ∈ Z} h̲_μ(T, x)` and the same for `h̄`, over Borel probability
  measures, the minimum attained by a purely atomic measure.
  `lowerEntropy_eq_iInf_measure`, `upperEntropy_eq_iInf_measure` (stated for every `Z`,
  including `Z = ∅`), `exists_atomic_measure_lowerEntropy_eq`,
  `exists_atomic_measure_upperEntropy_eq` (the minimizer is the normalized `m^A`, null outside
  a countable set).

Remarks 6.13 and 6.15 are not formalized.

## 4. Domination and decompositions (§7.2, and Propositions 6.3, 6.4)

Files: `PointToSet/Measure/Domination.lean`, `Decomposition.lean`. These are classical: no
oracle appears. The space is a second-countable metric space with its Borel σ-algebra.

* **`meas:domination`** (Lemma 7.1) — for `ν`-almost every `x`,
  `μ(B_n(x, T, ε)) ≤ n² ν(B_n(x, T, 2ε))` for all large `n`; consequently `Φ_ν ≤ Φ_μ`
  coordinatewise, `ν`-almost everywhere. `μ` is finite, `ν` arbitrary.
  `ae_eventually_measure_bowenBall_le`, `ae_localEntropyAt_le`, `ae_localEntropy_le`
  (`Domination.lean`).
* **`meas:abs-cont`** (Proposition 6.4) — ◇ proved from Lemma 7.1 instead of the randomness
  argument of the sketch. `ae_localEntropy_eq_of_absolutelyContinuous`,
  `entropyLaw_eq_map_of_absolutelyContinuous`, `entropyLaw_absolutelyContinuous`
  (`Decomposition.lean`).
* **`meas:affine`** (Proposition 6.3, Corollary 6.5(a) for countable combinations) — ◇ proved
  from Proposition 6.4. The combination is `Measure.sum fun j ↦ t j • μs j` over a countable
  index type with all `t j ≠ 0`. `ae_localEntropy_eq_of_sum`, `entropyLaw_sum`,
  `measureEntropy_sum` (`Decomposition.lean`).
* **`meas:integral`** (Theorem 7.3) — the decomposition `μ = ∫ μ_ω dQ(ω)` is a finite kernel
  `κ : Kernel Ω X` and a finite measure `Q` on a measurable space `Ω` (no standard Borel
  assumption is needed); `μ = Q.bind κ`, `M = Q ⊗ₘ κ`.
  (a) `ae_compProd_localEntropy_le`; (b) `kernelEntropyLaw_eq_iff`;
  (c) `lintegral_measureEntropy_le`; joint measurability `measurable_localEntropy_kernel`
  (`Decomposition.lean`).

Remark 7.2 is not formalized.

## 5. Essential bounds and variational forms (§4.1, §4.2, Corollary 6.5(c))

Files: `PointToSet/Measure/EffectiveNull.lean`, `EssentialBounds.lean`, `Variational.lean`.

* **`meas:effective-null`** — list intersections of c.e. open families are c.e. open
  (`IsCeOpenFamilyIn.biInter_list`); a `μ`-null `A`-effectively closed set contains no random
  point (`randomPoints_subset_of_isCeOpenIn`); every null set is avoided by the random points
  of an upper cone of oracles (`exists_oracle_randomPoints_disjoint`).
* **`meas:feng-huang`** (Proposition 4.1) — `measureEntropy_eq_lintegral_orbitComplexities`.
* **`meas:essential`** (Theorem 4.3) — (a) `iSup_randomPoints_orbitComplexities_fst`,
  `lowerEntropy_randomPoints`, `essSup_lowerLocalEntropy_eq_iInf_lowerEntropy`;
  (b) `essSup_upperLocalEntropy_le_iSup_randomPoints`, `exists_cone_iSup_randomPoints_snd`,
  `essSup_upperLocalEntropy_eq_iInf_oracle`, `essSup_upperLocalEntropy_eq_iInf_upperEntropy`;
  (c) `iInf_randomPoints_orbitComplexities_le_essInf`, `exists_cone_iInf_randomPoints`,
  `essInf_localEntropy_eq_iSup_oracle`, `essInf_localEntropy_eq_iInf_entropy`. Sets `Z` are
  arbitrary and `μ Z` is the outer measure. Helpers: `measure_randomPoints_eq_one`,
  `essSup_lowerLocalEntropy_le_lowerEntropy`, `essSup_upperLocalEntropy_le_upperEntropy`,
  `orbitComplexityAt_fst_le_essSup_of_mem_randomPoints`.
* **`meas:variational`** (Corollaries 4.2 and 6.5(c)) — the easy half of the Feng–Huang
  variational principle is proved from Theorem 4.3 (`measureEntropy_fst_le_lowerEntropy`,
  `measureEntropy_snd_le_upperEntropy`); the hard half is an outside input (open leaves
  `lowerEntropy_le_iSup_measureEntropy`, `upperEntropy_le_iSup_measureEntropy`). Derived from
  it: `lowerEntropy_eq_iSup_measureEntropy`, `upperEntropy_eq_iSup_measureEntropy`,
  `iInf_iSup_orbitComplexities_eq_iSup_lintegral` (Corollary 4.2),
  `lowerEntropy_eq_iSup_essInf`, `lowerEntropy_eq_iSup_essSup` (Corollary 6.5(c)).
* **`meas:chain`** (§4.4) — `essInf_le_measureEntropy_fst`, `measureEntropy_snd_le_essSup`,
  `entropy_chain` (no outside input).

Remark 4.4, Question 4.5 and the weak-2-randomness part of its answer are not stated; the
answer itself is Example 5.5 (section 9).

## 6. Information rates (§4.3, §6.2, §6.4)

Files: `PointToSet/Measure/InformationRate.lean`, `ProbabilityRate.lean`.

* **`meas:information-rate`** — `bowenInformation` (`I_n(μ, ε)`), `informationRateAt`,
  `informationRate` (`H̲_μ(T)`, `H̄_μ(T)`), `expectedOrbitComplexity`;
  `measurable_orbitComplexityNat`, `measurable_orbitComplexities`, `measurable_testFunction`.
* **`meas:expected-complexity`** (Proposition 4.6) —
  `bowenInformation_le_expectedOrbitComplexity` (every oracle, every Borel probability
  measure), `expectedOrbitComplexity_le_bowenInformation`,
  `informationRate_eq_expectedOrbitComplexity_rate`.
* **`meas:comparison`** (Proposition 4.7) — `measureEntropy_fst_le_informationRate_fst`,
  `informationRate_fst_le_snd`, and on a compact space
  `informationRate_snd_le_measureEntropy_snd`, through the uniform integrability estimate
  `exists_setLIntegral_localEntropyRate_le`.  ✎ the estimate has the tail term the sketch
  omits (see "Differences").
* **`meas:finite-time-affinity`** (Proposition 6.16) — `expectedOrbitComplexity_sum`,
  `bowenInformation_sum_le`, `sum_bowenInformation_le`. Remark 6.17 is not stated.
* **`meas:probability-rate`** (Proposition 6.10) — `lowerProbRate`, `upperProbRate`;
  `essInf_localEntropyAt_le_lowerProbRate`, `lowerProbRate_le_informationRateAt`,
  `upperProbRate_le_essSup_localEntropyAt`, `informationRateAt_le_upperProbRate` (compact),
  `iSup_lowerProbRate_orbitComplexity`, `iSup_upperProbRate_orbitComplexity`.

## 7. The universal map and statistics of the entropy law (§6, first half)

File: `PointToSet/Measure/EntropyLaw.lean`.

* **`meas:universal-map`** (Proposition 6.2, Remark 3.5) — `orbitComplexities_mono_oracle`,
  `entropyLaw_eq_map_orbitComplexities`,
  `localEntropy_le_orbitComplexities_of_mem_randomPoints`. The counterexample `μ = δ_y` of
  Remark 3.5 is not stated.
* **`meas:statistics`** (Corollary 6.5(a), (b)) — `measureEntropy_eq_lintegral_entropyLaw`,
  `essSup_localEntropy_eq_essSup_entropyLaw`, `essSup_localEntropy_sum`,
  `essInf_localEntropy_sum`, with `essSup_sum_measure`, `essInf_sum_measure`.

Remarks 6.6, 6.7, 6.9, 6.13, 6.15 and the list of §6.2 are not stated.

## 8. Integral affinity and pressure (§7.3, §8)

Files: `PointToSet/Measure/IntegralAffinity.lean`, `LocalPressure.lean`, `LocalPressureAux.lean`,
`PressurePointwise.lean`.

* **`meas:integral-affinity`** (Theorem 7.5) — (a)
  `ae_compProd_localEntropy_eq_of_absolutelyContinuous`, with the equivalence
  `compProd_absolutelyContinuous_prod_iff`; (c) `ae_compProd_localEntropy_eq_of_ratio`, the
  hypothesis written as "for every `δ > 0`, eventually
  `μ_ω(B_n(x, ε')) ≤ 2^{δn} μ(B_n(x, ε))`"; (b) the open leaf
  `ae_compProd_localEntropy_eq_of_ergodicDecomposition`. ◇ in (b) the entropy of a component
  is its Feng–Huang entropy (Mathlib has no Kolmogorov–Sinai entropy) and the hypothesis
  `h_μ(T) < ∞` is `h̄_μ(T) < ∞`. Remark 7.9 is not stated.
* **`meas:local-pressure`**, **`meas:weights`** (Definition 8.1, Lemma 8.2) —
  `localPressure`, `localBSDimension` and their fixed-scale versions; `localBSDimension_one`,
  `localPressure_zero`, `localPressure_smul`, `localBSDimension_smul`;
  `abs_finiteScalePressureCost_sub_le`, `pointwisePressure_eq_orbitPressureRate`,
  `pointwiseBSDimension_eq_orbitBSRate`.
* **`meas:pressure-pointwise`** (Theorem 8.3) — `pointwisePressure_le_localPressure`,
  `pointwiseBSDimension_le_localBSDimension`, `pointwisePressure_eq_localPressure`,
  `pointwiseBSDimension_eq_localBSDimension`,
  `pointwisePressure_eq_localPressure_universalMeasure`,
  `pointwiseBSDimension_eq_localBSDimension_universalMeasure`. The hypothesis
  `inf_n S_n φ(x)/n > -∞` is `BirkhoffBoundedBelow`; `u̲(x) > 0` is
  `0 < lowerBirkhoffAverage T u x`.
* **`meas:pressure-billingsley`**, **`meas:pressure-dual`** (Corollary 8.4) — eight
  Billingsley-type bounds (`lowerPressure_le_of_localPressure_le`, …,
  `le_upperBSDimension_of_le_localBSDimension`) and four dual principles
  (`lowerPressure_eq_iInf_measure`, `upperPressure_eq_iInf_measure`,
  `lowerBSDimension_eq_iInf_measure`, `upperBSDimension_eq_iInf_measure`), for pressure data
  `D : PressureData X`. Remark 8.5 is not stated.

## 9. Examples on shifts (§5, §6.1, §7)

Files: `PointToSet/Measure/Shift.lean`, `ShiftBernoulli.lean`, `ShiftProduct.lean`,
`ShiftAntiPhase.lean`, `ShiftBaire.lean`, `RandomNonAtom.lean`. Blueprint nodes `meas:shift`,
`meas:examples`. Cantor space carries `cantorMetricSpace` (`dist = (1/2)^firstDiff`) as a
local instance; entropies are in bits.

* **`meas:shift`** — `shiftMap`; `bowenBall_shiftMap_eq_cylinder`
  (`B_n(x, σ, β^k) = [x↾(n+k)]`); `localEntropy_shiftMap`, `informationRate_shiftMap`
  (cylinder formulas); `localEntropy_dirac`.
* **Example 5.1** — `productBernoulli`; `informationRate_productBernoulli`;
  `ae_localEntropy_productBernoulli`, `entropyLaw_productBernoulli` (through the strong law
  `ae_tendsto_avg_of_iIndepFun_bounded` for independent bounded variables, proved from fourth
  moments); the concrete case `entropyAverages_blockBias`, `entropyAverages_blockBias_lt`,
  `entropyLaw_blockBias`, `informationRate_blockBias` (`a̲ = (1+2a)/3 < ā = (2+a)/3`). The
  statement about every random sequence ([AHLM]) is not stated.
* **Example 5.2** — `antiPhaseMixture`; `entropyLaw_antiPhaseMixture`,
  `informationRate_antiPhaseMixture`, `antiPhaseMixture_strict`
  (`h̲_μ < H̲_μ = H̄_μ < h̄_μ`). The mutual singularity of the components (Kakutani) is not
  stated and not used.
* **Example 5.3** — `bernoulliMixture`; `ae_localEntropy_bernoulliMeasure`,
  `entropyLaw_bernoulliMeasure`, `informationRate_bernoulliMeasure`;
  `entropyLaw_bernoulliMixture`, `measureEntropy_bernoulliMixture`,
  `essInf_essSup_bernoulliMixture`, `lowerEntropy_randomPoints_bernoulliMixture`,
  `informationRate_bernoulliMixture`. The identification with the Kolmogorov–Sinai entropy is
  not stated.
* **Example 5.4** — `baireMeasure` on `ℕ → ℕ` (`baireMetricSpace`);
  `ae_localEntropy_baireMeasure`, `informationRate_baireMeasure`,
  `measureEntropy_snd_lt_informationRate_snd_baireMeasure`,
  `exists_measure_measureEntropy_lt_informationRate`; `informationRate_baireMeasureOf_cube`
  (infinite rates), `baireMeasureOf_compl_baireSupport` (compact support),
  `tendsto_baireMeasureOf_baireCompact`. ◇ the rates in probability are `0` in the form of
  the defining limits (`tendsto_measure_lt_localEntropyRate_baireMeasureOf`,
  `tendsto_measure_localEntropyRate_lt_baireMeasureOf`). The bound on spanning numbers is not
  stated.
* **Example 5.5** — ◇ the two constructions from a left-c.e. random real are the open leaves
  `exists_countable_atomic_random_upperLocalEntropy_eq_one` and
  `exists_random_lowerLocalEntropy_eq_zero`; the presentation of Cantor space is quantified
  existentially and "computable" is admissibility of the empty oracle. Proved from them:
  `exampleFiveFive_upper`, `exampleFiveFive_lower`, `not_forall_iSup_randomPoints_eq_essSup`,
  `not_forall_iInf_randomPoints_eq_essInf`. Proved outright:
  `ae_localEntropy_eq_zero_of_countable`, `localEntropy_map_uniformMeasure_le_one`,
  `one_le_upperLocalEntropy_of_frequently`.
* **Example 6.8** — `antiPhaseSegment`; `entropyLaw_antiPhaseSegment` (the same law for every
  `t`), `informationRate_antiPhaseSegment`
  (`(1+a)/2 ∓ |2t-1|(1-a)/6`).

## 10. Decompositions on shifts (§7)

Files: `PointToSet/Measure/Shift.lean`, `ShiftDecomposition.lean`, `ShiftDecompositionAux.lean`,
`ShiftSmoothAux.lean`, `ShiftGeneric.lean`.

* **Example 7.4** — (1) `entropyLaw_uniformMeasure_shiftMap`, `map_localEntropy_compProd_id`,
  `map_localEntropy_compProd_id_ne_entropyLaw`; (2) `gapKernel`, `localEntropy_gapKernel`,
  `bind_gapKernel`, `integralAffinity_gapKernel_iff`; (3) `fibreMap`, `diagMeasure`,
  `diagKernel`, `localEntropy_diagKernel`, `localEntropy_diagMeasure`,
  `map_localEntropy_diagKernel_ne_entropyLaw`.
* **Proposition 7.6** — `infoDensity`; (i) `ae_neg_logb_eq_add_infoDensity`,
  `ae_eventually_neg_two_logb_le_infoDensity` (cylinder form of the domination lemma,
  `ae_eventually_measure_cylinder_le`); (ii) `integralAffinity_of_tendsto_infoDensity`,
  `integralAffinity_iff_tendsto_infoDensity`; (iii)
  `ae_tendsto_infoDensity_of_absolutelyContinuous` (Lévy's upward theorem along cylinders).
  The identity `∫ i_n dM = I(ω; x↾n)` is not stated.
* **Remark 7.7** — `ae_infoDensity_le_smoothFamily`, `integralAffinity_smoothFamily`.
* **Example 7.8** — `revealKernel`; `ae_localEntropy_revealKernel` (`Φ_{μ_ω} = (1/2, 1)`),
  `integral_infoDensity_revealKernel_le` (`≤ 12 n / log₂ n`),
  `ae_frequently_half_le_infoDensity_revealKernel`,
  `map_localEntropy_revealKernel_ne_entropyLaw`.
* **Proposition 7.10** — `blockEntropy`, `shiftEntropy` (`inf_k H_ν(ξ^k)/k`, standing for the
  Kolmogorov–Sinai entropy of a shift-invariant measure), `IsGenericPoint`; both parts are
  open leaves: `upperOrbitComplexity_le_shiftEntropy`, `orbitComplexities_eq_shiftEntropy`.
  ✎ both carry the added hypothesis that the symbols of the ideal points of the presentation
  are computable relative to the oracle; the note leaves the presentation implicit.
  Remark 7.11 is not stated.

## Open leaves (`sorry`)

Seven declarations are stated and not proved. Eleven more are proved from them and inherit
the dependency; all other declarations of the chapter are free of it.

Outside inputs (theorems available neither in Mathlib nor in this library):

* `ae_compProd_localEntropy_eq_of_ergodicDecomposition` (`IntegralAffinity.lean`) —
  Theorem 7.5(b): needs the Brin–Katok theorem and Jacobs' theorem on the entropy of an
  ergodic decomposition.
* `lowerEntropy_le_iSup_measureEntropy`, `upperEntropy_le_iSup_measureEntropy`
  (`Variational.lean`) — the hard half of the Feng–Huang variational principle for the Bowen
  and packing entropies of a compact set. Derived from them:
  `lowerEntropy_eq_iSup_measureEntropy`, `upperEntropy_eq_iSup_measureEntropy`,
  `iInf_iSup_orbitComplexities_eq_iSup_lintegral`, `lowerEntropy_eq_iSup_essInf`,
  `lowerEntropy_eq_iSup_essSup`.
* `orbitComplexities_eq_shiftEntropy` (`ShiftGeneric.lean`) — Proposition 7.10(ii): V'yugin's
  effective ergodic theorem in Hoyrup's form, relativized.

Not yet proved (no outside theorem is missing, only work):

* `exists_countable_atomic_random_upperLocalEntropy_eq_one`,
  `exists_random_lowerLocalEntropy_eq_zero` (`RandomNonAtom.lean`) — the two constructions of
  Example 5.5. Missing: a computable presentation of Cantor space, the map `f` built from the
  approximations of a left-c.e. random real with the computability of `λ ∘ f⁻¹` in the sense
  of this chapter, the transfer of randomness from the library's Cantor-space definition to
  `randomPoints` and along `f`, and the cylinder estimates at `f(Ω)`. Derived from them:
  `exampleFiveFive_upper`, `exampleFiveFive_lower`, `exists_iSup_randomPoints_gt_essSup`,
  `not_forall_iSup_randomPoints_eq_essSup`, `exists_iInf_randomPoints_lt_essInf`,
  `not_forall_iInf_randomPoints_eq_essInf`.
* `upperOrbitComplexity_le_shiftEntropy` (`ShiftGeneric.lean`) — Proposition 7.10(i): the
  block-coding (method of types) argument.

## Not stated

* Remarks: 3.4, the counterexample of 3.5, 4.4, 6.6, 6.7, 6.9, 6.13, 6.15, 6.17, 7.2, 7.9,
  7.11, 8.5; the list of §6.2; the summary table of §4.4 (its chain of inequalities is
  `entropy_chain`).
* Question 4.5 beyond Example 5.5 (the weak 2-randomness statement on shifts).
* In the examples: the statement of Example 5.1 about every random sequence, the mutual
  singularity in Example 5.2, the Kolmogorov–Sinai identification in Example 5.3, the spanning
  numbers in Example 5.4, and the mutual-information identity of Proposition 7.6(i).
* §9 (relation to the literature, questions).

## Differences from the note found while formalizing

No statement of the note that is proved here was found to be false.

* **Proposition 4.7, sketch.** The bound `∫_{f_n > M} f_n dμ ≤ r_n M 2^{-Mn}` is not justified
  as written: `f_n` is unbounded above `M` on that set. The correct bound has a tail term,
  `r_n 2^{-Mn} (M + 2)`; it still tends to `0` uniformly in `n`, and the conclusion holds
  (`exists_setLIntegral_localEntropyRate_le`).
* **Lemma 3.2.** The multiplicative form of the inequality used here needs `t_ε(x) < ∞`; the
  additive form of the note is then the vacuous `∞ ≤ ∞`.
* **Lemma 3.1, Theorem 3.3(i), Theorem 8.3(i).** They hold for every `A`-computable measure
  of total mass at most one; this makes Proposition 6.12 and Theorem 8.3(iii) instances.
* **Propositions 6.3 and 6.4.** They follow from Lemma 7.1 without oracles or randomness.
* **Theorem 7.3.** No standard Borel assumption on the label space is needed.
* **Corollaries 6.14 and 8.4(c).** The dual principles hold for every set, including the empty
  one.
* **Proposition 4.6.** The first inequality holds for every oracle and every Borel
  probability measure (as the sketch of Proposition 6.16 notes).
* **Example 5.3.** `H(p) ≤ H(q)` suffices for the essential bounds; the entropy law and the
  rates need no ordering.
* **Example 6.8, Remark 7.7.** The constants of the proofs differ from those of the sketches
  (mean information within `H(t)` of the average; radius `1/(kn)` instead of `1/n`); the
  statements are those of the note.
* **Proposition 7.10.** A hypothesis on the presentation is needed (see section 10).

## Remarks (in progress, paused 11 November 2026)

Work on formal statements for the remarks was started and stopped early. Two partial files
exist, `PointToSet/Measure/RemarksRates.lean` (Remarks 6.9, 6.17, 8.5 and the Bernoulli
sentence of 7.2) and `PointToSet/Measure/RemarksShift.lean` (Remarks 3.4, 6.6, 6.7, 7.11).
They have not been checked, may not compile, and are not imported by `KolmogorovMathlib.lean`.
`PointToSet/Measure/Remarks.lean` (Remarks 3.5, 4.4, 6.13, 6.15, 7.2, 7.9) was not yet created.
The plan for each remark is a formal statement, a proof where little new infrastructure is
needed, and otherwise a tracked `sorry` whose docstring lists the prerequisites.
