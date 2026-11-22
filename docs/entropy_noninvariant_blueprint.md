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
(sections 5–10 below). The remarks are in section 11. Since 18 November 2026 every statement is
proved ("Open leaves" is empty and records what was closed); what is not stated at all is listed
under "Not stated".

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

## Status (18 November 2026)

The chapter has no `sorry`. The seven open leaves recorded on 17 November are proved (see "Closed
since 11 November" below): later on 17 November both directions of the exact Levin–Schnorr form of
Remark 3.4, the word-level comparison of Remark 6.6, the values of Remark 7.2 at every random
point and the comparison of Remark 8.5 that the note marks as unchecked; on 18 November both
constructions of Example 5.5. An audit of the formalization against the note (18 November) led to
further statements: Corollary 8.4(c) with its purely atomic minimizers; Example 5.5 stated on the
standard computable presentation `cantorPresentation` of Cantor space instead of an existentially
quantified presentation; and Proposition 7.10 and Remarks 3.4, 6.6, 7.11 at `cantorPresentation`
for every oracle, without the hypothesis on the presentation. New mathematics: Jacobs' theorem on
the entropy of an integral decomposition, with its consequences that the Feng–Huang entropy of
every invariant measure on a compact metric space is its Kolmogorov–Sinai entropy (the mean of
`Λ_μ` in Remark 6.7) and that the mixture of Example 5.3 has Kolmogorov–Sinai entropy
`(H(p) + H(q))/2`; the identity of `shiftEntropy` with the Kolmogorov–Sinai entropy on shifts; and
three modules `NoteSupplements.lean`, `NoteSupplementsAux.lean`, `NoteSupplementsLate.lean` with
sentences of §4.3, §4.4 and Examples 5.2, 5.4, 5.5, 6.8 that were not stated before (Example 5.2
only in part, see "Not stated").

Counts (18 November 2026): the chapter is 39 modules, about 18,100 lines,
807 public declarations; the companion modules (`Ergodic/`, `Measure/Ergodic/`)
are 53 modules, about 18,600 lines, 660 public declarations. `lake build
KolmogorovMathlib` succeeds with no warnings. Neither the chapter nor the companion modules
contain a `sorry`, and 0 declarations depend on one: by `#print axioms`, every declaration of
the chapter and of the companion modules depends only on `propext`, `Classical.choice` and
`Quot.sound`.

Earlier states. On 11 November: 34 modules, about 16,650 lines, 703 public declarations, all with
docstrings; `lake build` of the 34 modules succeeded with the 15 `sorry`s then open as the only
warnings; 37 public declarations (the 15 leaves and 22 statements derived from them) depended on
them. By 17 November `ae_localEntropy_eq_of_ergodic` (Remark 6.7) and both parts of
Proposition 7.10 were proved through `docs/ml_random_orbit_complexity_blueprint.md`, leaving 12
`sorry`s. Later on 17 November the four outside inputs were proved in companion modules: Theorem
7.5(b) (`ae_compProd_localEntropy_eq_of_ergodicDecomposition`), the non-ergodic Brin–Katok
statement of Remark 6.7 (`ae_localEntropy_fst_eq_snd_of_measurePreserving`), V'yugin's theorem
of Remark 7.11 (`exists_isGenericPoint_of_mem_randomPoints`) and the hard half of the Feng–Huang
variational principle (`lowerEntropy_le_iSup_measureEntropy`,
`upperEntropy_le_iSup_measureEntropy`); the hypothesis `h̄_μ(T) < ∞` of Theorem 7.5(b) and of
the non-ergodic Brin–Katok statement was dropped, and `VariationalPacking.lean` was added
(section 5). The chapter was then 35 modules, about 16,640 lines, 718 public declarations, with
7 `sorry`s on which 17 public declarations depended; the companion modules (41 modules, about
14,150 lines) had none.

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
  `exists_mem_randomPoints_of_measure_pos`; for an oracle computing the metric table, a point
  random for `a μ₁ + b μ₂` (`a + b ≤ 1`) is random for `μ₁` or for `μ₂`
  (`noteSupp_randomPoints_add_subset`, `NoteSupplements.lean`).
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

Remarks 3.4 and 3.5 are in section 11.

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

Remarks 6.13 and 6.15 are in section 11.

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

Remark 7.2 is in section 11.

## 5. Essential bounds and variational forms (§4.1, §4.2, Corollary 6.5(c))

Files: `PointToSet/Measure/EffectiveNull.lean`, `EssentialBounds.lean`, `Variational.lean`,
`VariationalPacking.lean`; the hard half of the variational principle is proved in
`PointToSet/Measure/Ergodic/FengHuangLower.lean`, `FengHuangLowerAux.lean`, `FengHuangUpper.lean`.

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
  `orbitComplexityAt_fst_le_essSup_of_mem_randomPoints`. In `NoteSupplements.lean`:
  `noteSupp_exists_cone_orbitComplexities_eq` (if `Φ_μ = c` almost everywhere, every random
  point relative to an oracle of an upper cone has orbit complexities `c`) and
  `noteSupp_orbitComplexities_fst_le_of_ae` (Theorem 4.3(a) at a single random point).
* **`meas:variational`** (Corollaries 4.2 and 6.5(c)) — the easy half of the Feng–Huang
  variational principle is proved from Theorem 4.3 (`measureEntropy_fst_le_lowerEntropy`,
  `measureEntropy_snd_le_upperEntropy`). The hard half (D.-J. Feng and W. Huang,
  J. Funct. Anal. 263 (2012), Theorems 1.2 and 1.3), `lowerEntropy_le_iSup_measureEntropy` and
  `upperEntropy_le_iSup_measureEntropy`, is proved (17 November 2026) in
  `Measure/Ergodic/FengHuangLower.lean` with `FengHuangLowerAux.lean`
  (`lowerEntropy_le_iSup_measureEntropy'`: a weighted Bowen content and a dynamical Frostman
  lemma `fhLower_frostman`, by Hahn–Banach and Riesz–Markov–Kakutani) and
  `Measure/Ergodic/FengHuangUpper.lean` (`upperEntropy_le_iSup_measureEntropy'`: a kernel of `K`
  none of whose relatively open pieces is thin for the modified upper capacity, a Cantor tree of
  `(n, 4ε)`-separated sets with the mass split equally among the children, and a weak-* cluster
  point of the level measures). Derived from it, and so unconditional:
  `lowerEntropy_eq_iSup_measureEntropy`, `upperEntropy_eq_iSup_measureEntropy`,
  `iInf_iSup_orbitComplexities_eq_iSup_lintegral` (Corollary 4.2),
  `lowerEntropy_eq_iSup_essInf`, `lowerEntropy_eq_iSup_essSup` (Corollary 6.5(c); each states
  the lower and the upper version).
  The chapter's `upperEntropy P T K` is the modified upper capacity entropy; the library
  identifies it with the packing topological entropy of Feng–Huang, the zero-potential packing
  pressure (`entropy_eq_zeroPotentialPressure_of_nonempty_upper` in
  `PointToSet/Pressure/Lower/EntropyZeroPotential.lean` and `pressureEquivalence_upper` in
  `PointToSet/PackingEquivalences/Pressure/Equivalence.lean`). With these,
  `packingPressure_zero_le_iSup_measureEntropy` (`VariationalPacking.lean`) states the hard half
  of Feng–Huang's Theorem 1.3 in their terms: the packing topological entropy of a nonempty
  compact set is at most the supremum of `h̄_μ(T)` over the probability measures with
  `μ(K) = 1`.
* **`meas:chain`** (§4.4) — `essInf_le_measureEntropy_fst`, `measureEntropy_snd_le_essSup`,
  `entropy_chain` (no outside input). "Every inequality can be strict" and "`ess sup h̲_μ` and
  `H̄_μ` are not comparable": `noteSupp_entropy_chain_strict` (for the measures of
  Examples 5.1, 5.2, 5.3) and `noteSupp_exists_entropy_chain_strict` (existential form)
  (`NoteSupplementsLate.lean`).

Remark 4.4 is in section 11. Question 4.5 and the weak-2-randomness part of its answer are not
stated; the answer itself is Example 5.5 (section 9).

## 6. Information rates (§4.3, §6.2, §6.4)

Files: `PointToSet/Measure/InformationRate.lean`, `ProbabilityRate.lean`; the sentences of
§4.3 and §6.2 in `NoteSupplements.lean`, `NoteSupplementsAux.lean`, `NoteSupplementsLate.lean`.

* **`meas:information-rate`** — `bowenInformation` (`I_n(μ, ε)`), `informationRateAt`,
  `informationRate` (`H̲_μ(T)`, `H̄_μ(T)`), `expectedOrbitComplexity`;
  `measurable_orbitComplexityNat`, `measurable_orbitComplexities`, `measurable_testFunction`.
  The two unnumbered claims of §4.3: `noteSupp_bowenInformation_le_refinementEntropy`
  (`I_n(μ, ε) ≤ H_μ(ξ^n)` for every finite Borel partition `ξ` of diameter less than `ε`, with
  `noteSupp_lintegral_infoBits_cell`: `∫ -log₂ μ(ξ(x)) dμ(x) = H_μ(ξ)`), and on a shift with
  `d_β` and the time-zero partition `I_n(μ, β^k) = H_μ(ξ^{n+k})` exactly for `n ≥ 1`
  (`noteSupp_bowenInformation_shiftMap_eq`, `noteSupp_bowenInformation_shiftMap_eq_blockEntropy`,
  `noteSupp_bowenInformation_shiftMap_eq_lintegral`).
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
  `bowenInformation_sum_le`, `sum_bowenInformation_le`. Remark 6.17 is in section 11.
* **`meas:probability-rate`** (Proposition 6.10) — `lowerProbRate`, `upperProbRate`;
  `essInf_localEntropyAt_le_lowerProbRate`, `lowerProbRate_le_informationRateAt`,
  `upperProbRate_le_essSup_localEntropyAt`, `informationRateAt_le_upperProbRate` (compact),
  `iSup_lowerProbRate_orbitComplexity`, `iSup_upperProbRate_orbitComplexity`. The §6.2
  sentence on Example 6.8 (for `0 < t < 1` the rates in probability are `(1+2a)/3` and
  `(2+a)/3`, independent of `t`): `noteSupp_probRates_antiPhaseSegment` (every scale),
  `noteSupp_iSup_probRates_antiPhaseSegment` (supremum over scales), through
  `noteSupp_lowerProbRate_eq_of_tracks`, `noteSupp_upperProbRate_eq_of_tracks` and
  `noteSupp_tracks_productMixture` (rates in probability of a two-component mixture of product
  measures; no mutual singularity is used).

## 7. The universal map and statistics of the entropy law (§6, first half)

File: `PointToSet/Measure/EntropyLaw.lean`.

* **`meas:universal-map`** (Proposition 6.2, Remark 3.5) — `orbitComplexities_mono_oracle`,
  `entropyLaw_eq_map_orbitComplexities`,
  `localEntropy_le_orbitComplexities_of_mem_randomPoints`. The counterexample `μ = δ_y` of
  Remark 3.5 is `mem_randomPoints_dirac`, `exists_dirac_orbitComplexities_not_le`
  (`Remarks.lean`, section 11).
* **`meas:statistics`** (Corollary 6.5(a), (b)) — `measureEntropy_eq_lintegral_entropyLaw`,
  `essSup_localEntropy_eq_essSup_entropyLaw`, `essSup_localEntropy_sum`,
  `essInf_localEntropy_sum`, with `essSup_sum_measure`, `essInf_sum_measure`.

Remarks 6.6, 6.7, 6.9, 6.13, 6.15 are in section 11; the list of §6.2 ("three levels") is not
stated.

## 8. Integral affinity and pressure (§7.3, §8)

Files: `PointToSet/Measure/IntegralAffinity.lean`, `LocalPressure.lean`, `LocalPressureAux.lean`,
`PressurePointwise.lean`.

* **`meas:integral-affinity`** (Theorem 7.5) — (a)
  `ae_compProd_localEntropy_eq_of_absolutelyContinuous`, with the equivalence
  `compProd_absolutelyContinuous_prod_iff`; (c) `ae_compProd_localEntropy_eq_of_ratio`, the
  hypothesis written as "for every `δ > 0`, eventually
  `μ_ω(B_n(x, ε')) ≤ 2^{δn} μ(B_n(x, ε))`"; (b)
  `ae_compProd_localEntropy_eq_of_ergodicDecomposition`, proved (17 November 2026) in
  `Measure/Ergodic/ErgodicDecompositionEntropy.lean`
  (`ae_compProd_localEntropy_eq_measureEntropy_of_ergodicDecomposition`, and the
  Kolmogorov–Sinai form `ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition`) by an
  algorithmic route, without Jacobs' theorem: Theorem 7.3(a) and the ergodic Brin–Katok formula
  give `Φ_{μ_ω} = (h_ω, h_ω) ≤ Φ_μ`, and at `μ`-random points block coding along the itinerary of
  the point, which is generic for the coded ergodic component, bounds `h̄_μ(T, x)` by `h_ω`
  (`ae_compProd_upperLocalEntropy_le_ksEntropy`). ◇ in (b) the entropy of a component is stated
  as its Feng–Huang entropy (equal to its Kolmogorov–Sinai entropy, `measureEntropy_eq_ksEntropy`);
  the hypothesis `h_μ(T) < ∞` of the note (`h̄_μ(T) < ∞` in the first formalization) is not
  needed and was dropped. Integrated against the decomposition with Jacobs' theorem
  (18 November 2026, `Measure/Ergodic/KSInvariant.lean`):
  `jacobs_measureEntropy_bind_eq_lintegral_ksEntropy` (both Feng–Huang entropies of `μ` equal
  `∫ h_{κ ω}(T) dQ(ω)`). Remark 7.9 is in section 11.
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
  `D : PressureData X`. The minima are attained by purely atomic probability measures (null
  outside a countable set; the witness is a normalized universal measure `c • m^A`):
  `exists_atomic_measure_lowerPressure_eq`, `exists_atomic_measure_upperPressure_eq`,
  `exists_atomic_measure_lowerBSDimension_eq`, `exists_atomic_measure_upperBSDimension_eq`
  (18 November 2026). Remark 8.5 is in section 11.

## 9. Examples on shifts (§5, §6.1, §7)

Files: `PointToSet/Measure/Shift.lean`, `ShiftBernoulli.lean`, `ShiftProduct.lean`,
`ShiftAntiPhase.lean`, `ShiftBaire.lean`, `RandomNonAtom.lean`, `ExampleFiveFive.lean` (proofs in
`Measure/Ergodic/ExampleFiveFiveUpper.lean`, `ExampleFiveFiveLower.lean`,
`ExampleFiveFiveLowerAux.lean`, on the presentation of `Measure/Ergodic/CantorPresentation.lean`),
and the supplements `NoteSupplements.lean`, `NoteSupplementsLate.lean`. Blueprint nodes
`meas:shift`, `meas:examples`. Cantor space carries `cantorMetricSpace` (`dist = (1/2)^firstDiff`)
as a local instance; entropies are in bits.

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
  stated and not used. The algorithmic sentence (`NoteSupplementsLate.lean`, stated for every
  anti-phase segment `μ_t`; Example 5.2 is `t = 1/2` by `antiPhaseMixture_eq`): the expected
  complexity rate is `(1+a)/2` (`noteSupp_expectedOrbitComplexity_rate_antiPhaseMixture`,
  Bowen-ball form, every admissible oracle); a `μ`-random point is `μ₁`- or `μ₂`-random
  (`noteSupp_randomPoints_antiPhaseSegment_subset`, every oracle computing the metric table);
  `K̲^A ≤ (1+2a)/3` at every random point for every admissible oracle
  (`noteSupp_orbitComplexities_fst_antiPhaseSegment_le`); the full sentence on an upper cone of
  oracles: `K̲ = (1+2a)/3` and `K̄ = (2+a)/3` at every random point
  (`noteSupp_exists_cone_orbitComplexities_antiPhaseSegment`) and, with the complexity of the word
  on `cantorPresentation`, `liminf K(x↾n)/n ≤ (1+2a)/3 < (2+a)/3 ≤ limsup K(x↾n)/n`
  (`noteSupp_exists_cone_wordComplexity_antiPhaseSegment`); and the reduction to the
  components for an oracle admissible for both
  (`noteSupp_orbitComplexities_antiPhaseSegment_of_mem_randomPoints`). Partial: the sentence for
  every admissible oracle is not stated (see "Not stated").
* **Example 5.3** — `bernoulliMixture`; `ae_localEntropy_bernoulliMeasure`,
  `entropyLaw_bernoulliMeasure`, `informationRate_bernoulliMeasure`;
  `entropyLaw_bernoulliMixture`, `measureEntropy_bernoulliMixture`,
  `essInf_essSup_bernoulliMixture`, `lowerEntropy_randomPoints_bernoulliMixture`,
  `informationRate_bernoulliMixture`. The Kolmogorov–Sinai entropy of the mixture is
  `(H(p) + H(q))/2`: `jacobs_ksEntropy_bernoulliMixture` (18 November 2026,
  `Measure/Ergodic/KSInvariant.lean`, from Jacobs' theorem and `measureEntropy_bernoulliMixture`;
  `jacobs_bernoulliMixture_measurePreserving`).
* **Example 5.4** — `baireMeasure` on `ℕ → ℕ` (`baireMetricSpace`);
  `ae_localEntropy_baireMeasure`, `informationRate_baireMeasure`,
  `measureEntropy_snd_lt_informationRate_snd_baireMeasure`,
  `exists_measure_measureEntropy_lt_informationRate`; `informationRate_baireMeasureOf_cube`
  (infinite rates), `baireMeasureOf_compl_baireSupport` (compact support),
  `tendsto_baireMeasureOf_baireCompact`. ◇ the rates in probability are `0` in the form of
  the defining limits (`tendsto_measure_lt_localEntropyRate_baireMeasureOf`,
  `tendsto_measure_localEntropyRate_lt_baireMeasureOf`). The bound on spanning numbers is not
  stated. "Every `μ`-random point has orbit complexity `0`" (`NoteSupplements.lean`): for a
  presentation whose ideal points have `A`-computable symbols, every random point is eventually
  `0` and lies in the support (`noteSupp_baire_of_mem_randomPoints`, a Solovay-type test, since
  `∑ p_i < ∞` computably), so `Φ_μ(x) = (0, 0)` and `K̲^A = K̄^A = 0` there
  (`noteSupp_orbitComplexities_baireMeasure_of_mem_randomPoints`). Without the symbol hypothesis:
  `K̲^A = 0` at every random point for every admissible oracle
  (`noteSupp_orbitComplexities_baireMeasure_fst`) and both are `0` on an upper cone of oracles
  (`noteSupp_exists_cone_orbitComplexities_baireMeasure`).
* **Example 5.5** — on Cantor space with its standard computable presentation
  `cantorPresentation` (`Measure/Ergodic/CantorPresentation.lean`); "computable" is
  admissibility of the empty oracle. The two constructions from a left-c.e. random real,
  `exists_countable_atomic_random_upperLocalEntropy_eq_one` and
  `exists_random_lowerLocalEntropy_eq_zero` (`ExampleFiveFive.lean`), are proved (18 November
  2026) in `Measure/Ergodic/ExampleFiveFiveUpper.lean` and `ExampleFiveFiveLower.lean` (with
  `ExampleFiveFiveLowerAux.lean`); the infrastructure of `CantorPresentation.lean` gives
  admissibility of `λ ∘ f⁻¹` for a causal computable `f` (`cantorPres_isMeasureAdmissible`,
  `cantorPres_isMeasureAdmissible_map_uniformMeasure`) and transfers randomness along `f`
  (`cantorPres_map_mem_randomPoints_of_isMartinLofRandom`). Proved from them:
  `exampleFiveFive_upper`, `exampleFiveFive_lower`, `exists_iSup_randomPoints_gt_essSup`,
  `exists_iInf_randomPoints_lt_essInf` (all at `cantorPresentation`),
  `not_forall_iSup_randomPoints_eq_essSup`, `not_forall_iInf_randomPoints_eq_essInf` (negations
  of statements for every presentation). Proved outright: `ae_localEntropy_eq_zero_of_countable`,
  `localEntropy_map_uniformMeasure_le_one`, `one_le_upperLocalEntropy_of_frequently`
  (`RandomNonAtom.lean`). The almost-everywhere bound of 5.5(2) is proved in the form
  `-log₂ μ'[x↾n] ≥ n - k - O(1)` for `n` in the `k`-th block (see "Differences"). The last
  sentence ("`z`, `z'` are computable from `0′`, so they stop being random once the oracle
  computes it"): `noteSupp_exampleFiveFive_upper_not_random_of_jump`,
  `noteSupp_exampleFiveFive_lower_not_random_of_jump` (the witnesses are `0′`-computable non-atoms
  that are `∅`-random but not random relative to any oracle computing `0′`), from the limit lemma
  `noteSupp_computableInJump_of_limit` and `noteSupp_not_mem_randomPoints_of_computableIn`
  (`NoteSupplements.lean`).
* **Example 6.8** — `antiPhaseSegment`; `entropyLaw_antiPhaseSegment` (the same law for every
  `t`), `informationRate_antiPhaseSegment`
  (`(1+a)/2 ∓ |2t-1|(1-a)/6`). The rates in probability, `(1+2a)/3` and `(2+a)/3` for every
  `0 < t < 1`, are in section 6.

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
* **Proposition 7.10** — `blockEntropy`, `shiftEntropy` (`inf_k H_ν(ξ^k)/k`), `IsGenericPoint`.
  For every shift-invariant probability measure `shiftEntropy` is the Kolmogorov–Sinai entropy:
  `shiftKS_shiftEntropy_eq_ksEntropy` (18 November 2026, `Measure/Ergodic/ShiftKSEntropy.lean`;
  the cylinder partitions of length `k` have diameter `≤ β^k`, and Walters 8.3), so the
  proposition also holds in Kolmogorov–Sinai form (`shiftKS_upperOrbitComplexity_le_ksEntropy`,
  `shiftKS_orbitComplexities_eq_ksEntropy`). Both parts are
  proved (17 November 2026), in `Measure/Ergodic/Proposition710.lean`:
  `upperOrbitComplexity_le_shiftEntropy` (block coding), `orbitComplexities_eq_shiftEntropy`
  (Hoyrup's theorem, genericity of random points `isGenericPoint_of_mem_randomPoints`), with the
  transport `ShiftTransport`, the word/ideal-point translation `ShiftTranslation` and
  `ShiftRandomness` (see `docs/ml_random_orbit_complexity_blueprint.md`).
  ✎ both carry the added hypothesis that the symbols of the ideal points of the presentation
  are computable relative to the oracle; the note leaves the presentation implicit. For the
  standard presentation `cantorPresentation` of Cantor space this hypothesis holds for every
  oracle (`cantorPres_computableIn_symbols`), and `upperOrbitComplexity_le_shiftEntropy_cantor`,
  `orbitComplexities_eq_shiftEntropy_cantor` (`Measure/Ergodic/CantorInstances.lean`) state the
  proposition there as printed, for every oracle. Remark 7.11 is in section 11.

## 11. Remarks

Files: `PointToSet/Measure/Remarks.lean`, `RemarksRates.lean`, `RemarksShift.lean`; the proofs
that need more than the chapter are in companion modules under `Measure/Ergodic/` and `Ergodic/`.
Blueprint node `meas:remarks`. Every formal statement of the remarks is proved (since
18 November 2026).

* **Remark 3.4** — on Cantor space (`RemarksShift.lean`): `bowenBall_shiftMap_one_cantor`;
  `orbitComplexityNat_cylinder_le_infoBits` and
  `infoBits_cylinder_le_orbitComplexityNat_of_mem_randomPoints` (the two halves of Theorem 3.3
  for cylinders; the information is taken 3 symbols, resp. the complexity 1 symbol, further,
  because of the changes of scale in Lemmas 3.1 and 3.2). The exact Levin–Schnorr form with the
  complexity of the word `x↾n`, `abs_oracleComplexity_cantorPrefix_sub_infoBits_le`, is proved
  from `oracleComplexity_cantorPrefix_le_infoBits` (every point) and
  `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints` (random points), both proved
  in `Measure/Ergodic/CantorLevinSchnorr.lean` (17 November 2026): the coding direction by the
  coding theorem applied to the words of positive mass, the incompressibility direction from the
  word-level Levin–Schnorr bound of Hoyrup's theorem (`exists_infoBits_le_wordComplexity_add`),
  which has `O(1)`; the statement keeps the note's `O(log n)`. The statements carry the
  hypothesis that the symbols of the ideal points are `A`-computable; at `cantorPresentation` it
  is discharged for every oracle: `oracleComplexity_cantorPrefix_le_infoBits_cantor`,
  `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints_cantor`,
  `abs_oracleComplexity_cantorPrefix_sub_infoBits_le_cantor` (`CantorInstances.lean`).
* **Remark 3.5** — the lower bound is `localEntropy_le_orbitComplexities_of_mem_randomPoints`
  (section 7); the counterexample is `mem_randomPoints_dirac` and
  `exists_dirac_orbitComplexities_not_le` (`Remarks.lean`, proved).
* **Remark 4.4** — `exists_countable_null_ceClosed_cover` (the exceptional set of
  Theorem 4.3(a) is covered by countably many null effectively closed sets);
  `setOf_frequently_lt_eq_iInter_cheapBalls`, `setOf_lowerOrbitComplexity_lt`,
  `setOf_frequently_le_eq_iInter_iUnion`, `setOf_lt_upperOrbitComplexity` (the shapes of the
  exceptional sets of (b), (c)); `measure_setOf_essSup_lt_upperOrbitComplexity`,
  `measure_setOf_lowerOrbitComplexity_lt_essInf`; all proved.
  `exists_null_upper_exceptional_meets_randomPoints`,
  `exists_null_lower_exceptional_meets_randomPoints` (Martin-Löf randomness does not avoid
  these null sets) are derived from Example 5.5 (proved); they quantify the presentation
  existentially, with witness `cantorPresentation`.
* **Remark 6.6** — (`RemarksShift.lean`)
  `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le`
  (`-log₂ m^A[w] = K^A(w) + O(log |w|)` on Cantor space, for every oracle `A` computing the
  symbols of the ideal points; proved in `Measure/Ergodic/UniversalMeasureWords.lean`, 17 November
  2026); for the empty oracle `abs_oracleComplexity_empty_sub_KA_le`
  (`K(w) = -log₂ M(w) + O(log |w|)` for the library's universal continuous semimeasure) and
  `orbitComplexities_eq_rates_KA` (`Ψ^∅` is the pair of growth rates of `KA` along prefixes),
  proved from the two. At `cantorPresentation`:
  `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le_cantor`,
  `orbitComplexities_eq_rates_KA_cantor` (no hypothesis left; `CantorInstances.lean`).
* **Remark 6.7** — the Brin–Katok statements, both proved and both without the hypothesis
  `h̄_μ(T) < ∞` of the first formalization: `ae_localEntropy_eq_of_ergodic` (since 16 November
  2026, from Theorem 1 of the note *Orbit complexity of Martin-Löf random points equals
  entropy*, see `docs/ml_random_orbit_complexity_blueprint.md`; Hoyrup's theorem is proved there
  too) and the non-ergodic `ae_localEntropy_fst_eq_snd_of_measurePreserving` (since 17 November
  2026, `ae_localEntropy_fst_eq_snd_of_invariant` in `Measure/Ergodic/BrinKatokNonErgodic.lean`:
  the ergodic decomposition `Kolmogorov.Ergodic.exists_ergodicDecomposition` and
  Theorem 7.5(b)); proved from them:
  `ae_entropyLaw_fst_eq_snd`, `measureEntropy_fst_eq_snd_of_measurePreserving`,
  `entropyLaw_eq_dirac_of_ergodic`, `entropyLaw_sum_ergodic`
  (`Λ_μ = ∑ t_j δ_{(h_j, h_j)}`), `entropyLaw_eq_map_of_ergodicDecomposition`. In these
  statements `h_μ(T)` is the Feng–Huang entropy. That it is the Kolmogorov–Sinai entropy for
  every invariant `μ`, so that the mean of `Λ_μ` is `h_μ(T)` as the remark says, is
  `jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving` (18 November 2026,
  `Measure/Ergodic/KSInvariant.lean`, from Jacobs' theorem
  `Kolmogorov.Ergodic.jacobs_ksEntropy_bind` and the ergodic decomposition); in Kolmogorov–Sinai
  form: `jacobs_lintegral_entropyLaw_fst`, `jacobs_lintegral_entropyLaw_snd` (the mean of
  `Λ_μ`), `jacobs_entropyLaw_eq_dirac_ksEntropy_of_ergodic`,
  `jacobs_entropyLaw_sum_ergodic_ksEntropy`,
  `jacobs_entropyLaw_eq_map_ksEntropy_of_ergodicDecomposition`.
* **Remark 6.9** — `lintegral_infoBits_mixture_bounds`,
  `informationRate_mixture_isLeast_isGreatest` (`H̲ = min_{c ∈ C} ⟨t, c⟩`,
  `H̄ = max_{c ∈ C} ⟨t, c⟩`), `informationRate_mixture_fst_eq_snd_iff` (`RemarksRates.lean`,
  proved), under the added hypothesis that every cylinder of every component has positive mass.
  The hypothesis is that of the Gibbs inequality used in the proof
  (`lintegral_infoBits_cylinder_le`); the remark does not need it, and the form without it is
  not stated.
* **Remark 6.13** — `universalMeasure_bowenBall_ge_measure`,
  `localEntropy_universalMeasure_le`, `localEntropy_universalMeasure_eq_of_mem_randomPoints`
  (`Remarks.lean`, proved).
* **Remark 6.15** — `exists_cone_iSup_orbitComplexities_le`,
  `iSup_orbitComplexities_eq_iSup_localEntropy_universalMeasure`,
  `lowerEntropy_eq_iInf_admissible`, `upperEntropy_eq_iInf_admissible` (`Remarks.lean`,
  proved).
* **Remark 6.17** — `informationRate_sum_eq`, `informationRate_fst_concave`,
  `informationRate_snd_convex` (`RemarksRates.lean`, proved; only finite entropy of the
  weights is needed).
* **Remark 7.2** — `orbitComplexities_eq_localEntropy_le_of_mem_randomPoints`
  (`Remarks.lean`, proved). Bernoulli sentence (`RemarksRates.lean`): `crossEntropyBits`,
  `binEntropy_div_log_two_le_crossEntropyBits`,
  `ae_localEntropy_bernoulliMeasure_crossEntropy`,
  `localEntropy_bernoulliMeasure_le_of_mem_randomPoints`. The values at every random point,
  `Φ_{ν_q}(x) = (H(q), H(q))` and `Φ_{ν_p}(x) = (H(q‖p), H(q‖p))`, are
  `localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints`, proved (17 November 2026)
  in `Measure/Ergodic/BernoulliRandom.lean`, where the statement now lives. Only admissibility
  for `ν_q` is used (the statement also carries admissibility for `ν_p`). The proof goes through
  the ergodicity of the Bernoulli shift (`bernRand_ergodic`, Kolmogorov's zero-one law) and an
  effective strong law (`bernRand_tendsto_freq`: at every `ν_q`-random point the frequency of
  ones tends to `q`), which needs no hypothesis on the ideal points: the cylinders
  `{y | y 0 = b}` are basic balls (`bernRand_isCeOpenIn_coord`).
* **Remark 7.7** — section 10.
* **Remark 7.9** — ✎ `ae_compProd_orbitComplexities_eq_bind`,
  `ae_orbitComplexities_eq_kernel` (fibrewise), `ae_compProd_orbitComplexities_eq_kernel`,
  `ae_compProd_orbitComplexities_kernel_le`, `kernelEntropyLaw_eq_iff_orbitComplexities`
  (jointly, under a measurability hypothesis; `measurable_orbitComplexities_of_countable`,
  `measurable_orbitComplexities_const`) (`Remarks.lean`, proved).
* **Remark 7.11** — V'yugin's theorem `exists_isGenericPoint_of_mem_randomPoints` is proved
  (17 November 2026; `exists_isGenericPoint_of_mem_randomPoints'` in
  `Measure/Ergodic/VyuginGenericity.lean`): Bishop's upcrossing inequality in V'yugin's
  potential form (`measureReal_upcrossesAtLeast_le`, `Ergodic/Upcrossing.lean`) makes the points
  whose frequency of a word upcrosses `[a, b]` at least `2^m c` times a `μ`-test, so all word
  frequencies converge at every random point (`exists_tendsto_frequency_of_mem_randomPoints`,
  `Measure/Ergodic/VyuginFrequencies.lean`; the computability of `μ` is not used); the limits
  define a shift-invariant probability measure for which `x` is generic, a cluster point of the
  empirical measures (`exists_isGenericPoint_of_tendsto_frequency`). Consequently
  `exists_isGenericPoint_upperOrbitComplexity_le`, proved from it and Proposition 7.10(i), is
  unconditional. Hoyrup's conclusion is the unasserted definition
  `RandomPointsInErgodicComponents`; its consequence
  `localEntropy_eq_shiftEntropy_of_randomPointsInErgodicComponents` is proved from
  Proposition 7.10(ii) (`RemarksShift.lean`). At `cantorPresentation`, for every oracle:
  `exists_isGenericPoint_of_mem_randomPoints_cantor`,
  `exists_isGenericPoint_upperOrbitComplexity_le_cantor` (`CantorInstances.lean`).
* **Remark 8.5** — `localBowenEquation` (at a random point `d̲_μ(x, T, u)` is finite and is the
  unique root of `P̲_μ(x, T, -s u) = 0`, and the same for the upper quantities),
  `staticPointDimensions_eq_localBSDimension_conformal` (on the conformal locus the
  algorithmic dimensions are the local BS dimensions), `localDimension` (`RemarksRates.lean`).
  The step the note marks as unchecked, `localBSDimension_eq_localDimension_conformal` (on the
  conformal locus the lower local BS dimension is the lower round-ball local dimension), is
  proved (17 November 2026) in `Measure/Ergodic/ConformalBallComparison.lean`, where the
  statement now lives. It is true as stated and holds for every measure, without randomness or
  admissibility (`confBall_localBSDimension_fst_eq_localDimension_fst`): Bowen balls lie between
  round balls of the orbit radii (`ballInclusion`), and the round-ball dimension is computed along
  those radii by nonmonotone scale sampling (`nonmonotoneScaleSampling`; both from
  `PointToSet/Conformal/Distortion/DistortionModuli.lean`).

## Open leaves (`sorry`)

None (18 November 2026). The chapter and the companion modules contain no `sorry`, and no
declaration depends on one.

### Closed since 11 November

All fifteen leaves of 11 November are proved. The proofs are in the companion modules
`KolmogorovMathlib/Ergodic/` and `KolmogorovMathlib/PointToSet/Measure/Ergodic/` (see
`docs/ml_random_orbit_complexity_blueprint.md`); the statements stay where they were, except
Proposition 7.10, the leaves of Remarks 7.2 and 8.5 (moved to the modules of their proofs) and
Example 5.5 (moved from `RandomNonAtom.lean` to `ExampleFiveFive.lean`).

* `upperOrbitComplexity_le_shiftEntropy`, `orbitComplexities_eq_shiftEntropy`
  (Proposition 7.10, 17 November) — block coding and Hoyrup's theorem,
  `Measure/Ergodic/Proposition710.lean` (section 10).
* `ae_localEntropy_eq_of_ergodic` (Remark 6.7, ergodic Brin–Katok, 16 November) — Theorem 1 of
  the companion note (`Measure/Ergodic/OrbitEntropy.lean`).
* `ae_compProd_localEntropy_eq_of_ergodicDecomposition` (Theorem 7.5(b), 17 November, formerly an
  outside input) — `Measure/Ergodic/ErgodicDecompositionEntropy.lean`, by block coding along the
  generic itinerary of the ergodic component at `μ`-random points; `h̄_μ(T) < ∞` dropped.
* `ae_localEntropy_fst_eq_snd_of_measurePreserving` (Remark 6.7, non-ergodic Brin–Katok,
  17 November, formerly an outside input) — `Measure/Ergodic/BrinKatokNonErgodic.lean`, from the
  ergodic decomposition `Kolmogorov.Ergodic.exists_ergodicDecomposition`
  (`Ergodic/ErgodicDecomposition.lean`, with Birkhoff's theorem without ergodicity,
  `Ergodic/BirkhoffNonErgodic.lean`) and Theorem 7.5(b); `h̄_μ(T) < ∞` dropped.
* `exists_isGenericPoint_of_mem_randomPoints` (Remark 7.11, V'yugin's theorem, 17 November,
  formerly an outside input) — `Ergodic/Upcrossing.lean`, `Measure/Ergodic/VyuginFrequencies.lean`,
  `Measure/Ergodic/VyuginGenericity.lean` (section 11); references: V. V. V'yugin, *Ergodic
  theorems for individual random sequences* (1997) and arXiv:2202.13465, §4.2.
* `lowerEntropy_le_iSup_measureEntropy`, `upperEntropy_le_iSup_measureEntropy` (the hard half of
  the Feng–Huang variational principle, 17 November, formerly an outside input) —
  `Measure/Ergodic/FengHuangLower.lean`, `FengHuangLowerAux.lean`, `FengHuangUpper.lean`
  (section 5).
* `oracleComplexity_cantorPrefix_le_infoBits`,
  `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints` (Remark 3.4, 17 November) —
  `Measure/Ergodic/CantorLevinSchnorr.lean`.
* `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le` (Remark 6.6, 17 November) —
  `Measure/Ergodic/UniversalMeasureWords.lean`.
* `localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints` (Remark 7.2, 17 November) —
  `Measure/Ergodic/BernoulliRandom.lean`, with the ergodicity of the Bernoulli shift
  (`bernRand_ergodic`) and an effective strong law (`bernRand_tendsto_freq`).
* `localBSDimension_eq_localDimension_conformal` (Remark 8.5, 17 November) —
  `Measure/Ergodic/ConformalBallComparison.lean`; true as stated, for every measure.
* `exists_countable_atomic_random_upperLocalEntropy_eq_one`,
  `exists_random_lowerLocalEntropy_eq_zero` (Example 5.5, 18 November) —
  `Measure/Ergodic/ExampleFiveFiveUpper.lean`, `ExampleFiveFiveLower.lean`,
  `ExampleFiveFiveLowerAux.lean`, on the computable presentation `cantorPresentation`
  (`Measure/Ergodic/CantorPresentation.lean`), which the statements now name instead of an
  existentially quantified presentation (section 9).

## Not stated

* In the remarks: the effective Borel hierarchy relative to an oracle and weak 2-randomness
  (Remark 4.4, and the corresponding part of the answer to Question 4.5); in Remark 6.6, the
  comparison with a continuous a priori semimeasure relative to a general oracle (the library
  has none; the comparison of `-log₂ m^A[w]` with `K^A(w)` is stated for every oracle);
  Remark 6.9 without the positivity of the cylinders of the components, and its last sentences
  (dependence on the convex hull of `C`, the affinity criteria); the comparison with Cutler's
  duality principle (Remark 6.15); Hoyrup's theorems on effectively decomposable measures
  (Remark 7.11: they need the space of ergodic measures and the computability of the
  representing measure of the ergodic decomposition); the commentary sentences of Remarks 3.4
  and 8.5.
* The summary table of §4.4 (its chain of inequalities is `entropy_chain`, the strictness of each
  inequality `noteSupp_entropy_chain_strict`) and the list of §6.2 ("three levels").
* In the examples: the statement of Example 5.1 about every random sequence ([AHLM]); the mutual
  singularity in Example 5.2; the algorithmic sentence of Example 5.2 for every admissible oracle
  (it is stated on an upper cone of oracles; for a single oracle admissible for both components it
  reduces to the values of `Φ_{μ_i}` at every `μ_i`-random point, which needs an effective strong
  law for independent, non-identically distributed bits); in Example 5.4, `K̄^A = 0` at every
  random point for an admissible oracle that does not compute the symbols of the ideal points
  (the lower complexity and the cone version are stated), and the spanning numbers; the
  mutual-information identity of Proposition 7.6(i).
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
* **Proposition 7.10.** A hypothesis on the presentation is needed (see section 10); the
  standard presentation of Cantor space satisfies it for every oracle.
* **Remark 7.9.** "For `M`-almost every `(ω, x)`, `x ∈ R_A^μ ∩ R_{A_ω}^{μ_ω}`" is not
  justified for an arbitrary choice `ω ↦ A_ω`: the set of such pairs need not be measurable.
  It holds fibrewise, and jointly when `(ω, x) ↦ Ψ^{A_ω}(x)` is measurable (for instance for
  countably many labels, or one oracle for all components).
* **Remark 3.4.** In the chapter's vocabulary (Bowen balls about ideal points) the reduction to
  cylinders has shifts of the length (3 symbols and 1 symbol), inherited from the changes of
  scale of Lemmas 3.1 and 3.2; the exact form with the complexity of the word is proved
  separately. Its incompressibility direction holds with `O(1)` in place of the note's
  `O(log n)` (the word-level bound `exists_infoBits_le_wordComplexity_add`); the statement keeps
  `O(log n)`.
* **Remarks 6.17 and 6.9.** Finitely many components and finite information rates are not
  needed in Remark 6.17 (finite entropy of the weights suffices); Remark 6.9 is proved for
  components whose cylinders all have positive mass, a restriction of the proof, not of the
  remark.
* **Remark 8.5.** The comparison of the local BS dimension with the round-ball local dimension
  on the conformal locus, which the note marks as unchecked, is true as stated, and holds for
  every measure, without randomness.
* **Examples 5.2 and 5.4, "every random point".** Theorem 3.3 turns the almost-everywhere values
  of `Φ_μ` into orbit complexities only at random points where `Φ_μ` is known. In Example 5.4
  the values at every random point need a Solovay-type test (proved when the oracle computes
  the symbols of the ideal points); in Example 5.2 they need the values of `Φ_{μ_i}` at every
  `μ_i`-random point, an effective strong law for independent, non-identically distributed bits
  (not proved; the sentence is proved on an upper cone of oracles).
* **Example 5.5(2), sketch.** The almost-everywhere estimate
  `-log₂ μ'[f'(y)↾n] ≥ n - O(log n)` is not what is proved. The formalization (blocks
  `[N_k, N_{k+1})` with `N_k = k^{k+1}`) proves `-log₂ μ'[x↾n] ≥ n - k - O(1)` for `n` in the
  `k`-th block, the constant depending on the point, for the `μ'`-almost every `x` whose windows
  `[N_k, N_k + k + 1)` eventually all contain a `1` (Borel–Cantelli). Since `k = O(log n)` this
  is consistent with the note's estimate, and the conclusion `Φ_{μ'} = (1, 1)` almost everywhere
  is unchanged.
