# Blueprint: Orbit complexity of Martin-Löf random points equals entropy

Formalization of the 5-page note *Orbit complexity of Martin-Löf random points equals entropy*
(November 2026). Theorem 1: on a compact space with an `A`-computable presentation, for an
`A`-represented continuous map `T` and an `A`-computable `T`-invariant ergodic probability
measure `μ`, every point that is Martin-Löf random for `μ` relative to `A` has
`K̲^A(x, T) = K̄^A(x, T) = h_μ(T)`, the Kolmogorov–Sinai entropy (bits), also when
`h_μ(T) = ∞`.

## Where it is

* `KolmogorovMathlib/Ergodic/` — classical ergodic theory, namespace `Kolmogorov.Ergodic`, no
  Kolmogorov imports (9 modules, of which 4 serve the non-invariant note: the ergodic
  decomposition, Birkhoff's theorem without ergodicity, Bishop's upcrossing inequality, Jacobs'
  theorem).
* `KolmogorovMathlib/PointToSet/Measure/Ergodic/` — the computability side, namespace
  `Kolmogorov.PointToSet` (44 modules, of which 9 `Hoyrup*` modules prove Hoyrup's theorem,
  4 prove Proposition 7.10 of the non-invariant note, 7 prove its former outside inputs, and 11,
  added on 17 and 18 November 2026, prove its last open leaves and the consequences of Jacobs'
  theorem).

53 modules, about 18,600 lines, 660 public declarations (18 November 2026).
`lake build KolmogorovMathlib` succeeds with no warnings; the 53 modules contain no `sorry`, and
every declaration depends only on `propext`, `Classical.choice` and `Quot.sound` (`#print
axioms`). Theorem 1 is therefore proved without any external input, including the
relativization to an oracle that the note asserted ("the proofs relativize verbatim"). The
counts of 17 November were 41 modules, about 14,150 lines, 434 public declarations.

## Map from the note to the declarations

| Note | Declaration(s) | Module | Status |
|---|---|---|---|
| `h_μ(T, P)`, `h_μ(T)` | `entropyRate` (`inf_{n≥1} H_μ(P^n)/n`), `ksEntropy` (sup over partitions `Fin p → Set X`), `partitionEntropy`, `condEntropy`, `refinement`, `IsMeasurablePartition`, `Refines` | `Ergodic/PartitionEntropy` | definitions |
| basic entropy facts | `tendsto_refinementEntropy_div` (limit form, Fekete), `refinementEntropy_add_le`, `partitionEntropy_join_le`, `condEntropy_le_of_refines`, `condEntropy_le_partitionEntropy`, `entropyRate_le_add_condEntropy` (Walters 4.12(iv)), `entropyRate_congr_ae`, `entropyRate_comp_equiv`, `entropyRate_le_ksEntropy`, `entropyRate_le_logb_card` | `Ergodic/PartitionEntropy` | proved |
| (I4) Walters 8.3 | `exists_condEntropy_lt_of_diam_lt`, `lt_entropyRate_of_diam_lt`, `tendsto_entropyRate_ksEntropy` | `Ergodic/FinePartitions` | proved |
| maximal ergodic lemma and inequality | `setIntegral_nonneg_of_maximal` (Garsia), `measure_maximal_birkhoffAverage_le` | `Ergodic/MaximalInequality` | proved |
| Birkhoff, ergodic case | `ae_tendsto_birkhoffAverage` (pointwise, bounded measurable `g`), `tendsto_integral_abs_birkhoffAverage_sub` (`L¹`) | `Ergodic/MeanErgodic` | proved |
| binomial bound (Step 4 of (b)) | `choose_le_two_rpow_binEntropyBits`, `tendsto_binEntropyBits_zero` | `Ergodic/BinomialEntropy` | proved (not used by the final proof of (b)) |
| words, cylinder tests | `listCylinder`, `wordPrefix`, `IsWordTestIn`, `wordRandomPoints`, `IsComputableWordMeasureIn`, `wordComplexity` (`K^A(ω↾n)`) | `WordRandomness` | definitions, proved lemmas |
| (I1) null-sphere radii | `exists_nullSphere_radii`, `isCeOpenFamilyIn_ball_of_computableRadius`, `isCeOpenFamilyIn_dist_gt_of_computableRadius` | `NullSphere` | proved |
| Lemma 2 | `IsComputablePartitionIn`, `exists_computablePartition` (with a measurable partition `Q ⊇ U` of small diameter), `ae_eq_of_isComputablePartitionIn` | `ComputablePartition` | proved |
| Lemma 3 | `codingDomain`, `symbolicCode`, `codedMeasure`, `symbolCell`; (i) `randomPoints_subset_codingDomain`; (ii) `codedMeasure_wordCylinder`, `ergodic_codedMeasure`, `isComputableWordMeasureIn_codedMeasure`, `shiftEntropy_codedMeasure`; (iii) `symbolicCode_mem_wordRandomPoints` | `SymbolicCoding` | proved |
| (I2) random points are typical | `measure_le_liminf_visitFrequency` (I2′: lower visit frequency of an `A`-c.e. open set `≥ μ(U)`), `isGenericPoint_symbolicCode` | `TypicalPoints` | proved |
| (I3) `limsup` half (V'yugin) | `limsup_wordComplexity_le_shiftEntropy` (at generic sequences, every oracle) | `BlockCoding` | proved |
| (I3) `liminf` half (Hoyrup), binary | `shiftEntropy_le_liminf_wordComplexity_bool` (= `shiftEntropy_le_liminf_wordComplexity_bool_of_hoyrup`) | `SymbolicLowerBound`, `Hoyrup*` | proved (see below) |
| "Binary suffices in (I3)" | `shiftEntropy_le_liminf_wordComplexity` (finite alphabet from binary) | `SymbolicLowerBound`, `…Aux`, `…Effective` | proved from the leaf |
| Theorem 1(a) | `orbitComplexityAt_snd_le_ksEntropy` (every scale), `upperOrbitComplexity_le_ksEntropy` | `OrbitUpper` | proved |
| Theorem 1(b) | `exists_le_orbitComplexityAt_fst`, `ksEntropy_le_lowerOrbitComplexity` | `OrbitLower`, `OrbitLowerAux` | proved |
| Theorem 1 | `orbitComplexities_eq_ksEntropy` | `OrbitEntropy` | proved |
| consequences | `ae_localEntropy_eq_ksEntropy` (Brin–Katok for ergodic `μ`, every continuous `T` on a compact metric space), `measureEntropy_eq_ksEntropy` (Feng–Huang = Kolmogorov–Sinai for ergodic `μ`), `ae_localEntropy_eq_measureEntropy_of_ergodic`, `exists_presentation` | `OrbitEntropy` | proved |
| Remarks 4–7 | — | — | not stated (commentary; flows are not in the library) |

## Hoyrup's theorem

`shiftEntropy_le_liminf_wordComplexity_bool`: for an `A`-computable shift-invariant ergodic
probability measure `ν` on `ℕ → Bool` and `ω` Martin-Löf random for `ν` relative to `A` (cylinder
tests), `h_ν(σ) ≤ liminf_n K^A(ω↾n)/n`. This is the `liminf` half of M. Hoyrup, *The dimension of
ergodic random sequences* (STACS 2012, arXiv:1107.1149, Theorem 4.1, stated there for `{0,1}^ℕ`,
prefix complexity and no oracle), proved here relative to an arbitrary oracle. The route is
simpler than Hoyrup's:

| Step | Declaration(s) | Module |
|---|---|---|
| lower semicomputable functions on `ℕ → Bool` (r.e. suprema, shifts, Birkhoff sums) | `IsLscFunFamilyIn`, `IsLscFunIn`, `shiftAverage`, `IsLscFunFamilyIn.iSup`, `IsLscFunIn.shiftAverage`, `IsLscFunFamilyIn.sum_range`, … | `HoyrupBasic` |
| random sequences meet no null cylinder; Levin–Schnorr lower half `-log₂ ν[ω↾n] ≤ K^A(ω↾n) + c` | `listCylinder_wordPrefix_pos_of_mem_wordRandomPoints`, `exists_infoBits_le_wordComplexity_add` | `HoyrupBasic` |
| effective Poincaré recurrence (Bienvenu–Day–Hoyrup–Mezhirov–Shen, arXiv:1007.5249, Thm 7) | `exists_iterate_notMem_of_mem_wordRandomPoints` | `HoyrupPoincare`, `HoyrupPoincareAux` |
| effective upper Birkhoff bound for bounded lower semicomputable functions | `limsup_shiftAverage_le_lintegral` | `HoyrupBirkhoff` |
| conditional information `-log₂ ν[x₀ | x₁…x_j]`, telescoping, truncation | `condInfo`, `truncDefect`, `infoBits_cylinder_eq_sum_condInfo`, `sum_min_iInf_condInfo_le_infoBits`, `isLscFunIn_truncDefect` | `HoyrupCondInfo` |
| Chung's lemma `∫ sup_j condInfo ν j < ∞` | `lintegral_iSup_condInfo_lt_top` | `HoyrupChung` |
| a.e. convergence of `condInfo ν j` (supermartingale convergence) | `ae_exists_tendsto_condInfo` | `HoyrupMartingale` |
| `∫ condInfo ν j = H_{j+1} - H_j` and the entropy limit | `lintegral_condInfo`, `shiftEntropy_le_iSup_lintegral_min` | `HoyrupEntropyLimit` |
| lower half of effective Shannon–McMillan–Breiman; Hoyrup's theorem | `shiftEntropy_le_liminf_infoBits`, `shiftEntropy_le_liminf_wordComplexity_bool_of_hoyrup` | `HoyrupLower` |

Differences from Hoyrup's proof: only the lower bound is proved; truncating the conditional
information at a level `L` makes the remaining Birkhoff averages bounded, so the effective Doob
theorem, the effective Birkhoff theorem for unbounded and `Δ⁰₂` functions (Theorem 3.3,
Corollary 3.1, Proposition 4.2) and Birkhoff's theorem for unbounded functions are not needed.
Correction: the process `d(x₀…x_k) = ν[x₁…x_k]/ν[x₀…x_k]` that Hoyrup's Lemma 4.1 calls a
martingale is in general only a supermartingale (an extension `w b` with `ν[w b] = 0` and
`ν[w' b] > 0` loses mass); a.e. convergence still holds and is what is used.

## Differences from the note

* Kolmogorov–Sinai entropy is defined here (Mathlib has none) as the supremum of
  `inf_{n≥1} H_μ(P^n)/n` over finite measurable partitions; the limit form is proved.
* (I2) is used only in the form (I2′) above, proved without computable real functions: inner
  approximation of `U` by a finite union of closed balls, the mean ergodic theorem, a searched
  `N`, and the maximal inequality give a Martin-Löf test. The genericity of the itinerary
  `φ(x)` follows from (I2′) applied to the cells `O_w`. Birkhoff's pointwise theorem is
  formalized for bounded `g`: for ergodic `μ` in `Ergodic/MeanErgodic`, and since 17 November
  2026 without ergodicity, with the conditional expectation on the invariant σ-algebra as the
  limit (`ae_exists_tendsto_birkhoffAverage`, `ae_tendsto_birkhoffAverage_condExp`,
  `Ergodic/BirkhoffNonErgodic`); Theorem 1 uses only the ergodic case.
* The `limsup` half of (I3) (V'yugin) is not an input: it is proved by block coding at generic
  sequences, and genericity of `φ(x)` comes from (I2′).
* "Binary suffices": the formalization uses a one-hot code with `b = p` and proves only
  `h_ν(σ) ≤ p · h_{ν''}(σ)`; ergodicity of `ν''` is derived from that of `ν` directly.
* Step 4 of (b) encodes the side information as one list of optional symbols bounded by block
  coding instead of the binomial index; the binomial bound is proved but unused.
* `Continuous T` is redundant for Theorem 1(a) (measurability from ergodicity suffices).

## Proposition 7.10 of the note on non-invariant measures

Both parts of Proposition 7.10 of *Entropy of non-invariant measures and orbit complexity of
random points* (generic and random points of a shift with a first-difference metric and a
presentation whose ideal points have computable symbols) are proved in
`Measure/Ergodic/Proposition710.lean` (moved there from `ShiftGeneric.lean`, which the word-level
modules import): (i) `upperOrbitComplexity_le_shiftEntropy` from block coding, (ii)
`orbitComplexities_eq_shiftEntropy` from Hoyrup's theorem. Supporting modules:
`ShiftTransport` (recoding a finite alphabet into `Fin p`: measurability, word complexity up to
`O(1)`, shift entropy, genericity, ergodicity, randomness, computability), `ShiftTranslation`
(`K̄^A(x, σ) ≤ limsup K^A(x↾n)/n` and `liminf K^A(x↾n)/n ≤ K̲^A(x, σ)`), `ShiftRandomness`
(cylinders are c.e. open without computability of `β`, presentation randomness implies word
randomness, computable cylinder measures, genericity of random points of ergodic measures).

Blueprint node **`erg:prop710`** (also cited by two modules added on 18 November 2026):
`ShiftKSEntropy` proves that the entropy `shiftEntropy ν = inf_k H_ν(ξ^k)/k` used in
Proposition 7.10 is the Kolmogorov–Sinai entropy of every shift-invariant probability measure,
`shiftKS_shiftEntropy_eq_ksEntropy` (the cylinder partitions of length `k` have diameter
`≤ β^k`, so Walters 8.3 applies, and their entropy rates are at most that of the time-zero
partition), and states the proposition in Kolmogorov–Sinai form
(`shiftKS_upperOrbitComplexity_le_ksEntropy`, `shiftKS_orbitComplexities_eq_ksEntropy`).
`CantorInstances` instantiates Proposition 7.10 and Remarks 3.4, 6.6, 7.11 on Cantor space with
its standard presentation `cantorPresentation`, whose ideal points have computable symbols
relative to every oracle (`cantorPres_computableIn_symbols`), so the hypothesis on the
presentation disappears: `upperOrbitComplexity_le_shiftEntropy_cantor`,
`orbitComplexities_eq_shiftEntropy_cantor`,
`abs_oracleComplexity_cantorPrefix_sub_infoBits_le_cantor`, `orbitComplexities_eq_rates_KA_cantor`,
`exists_isGenericPoint_of_mem_randomPoints_cantor` and the other `*_cantor` statements.


## The former outside inputs of the note on non-invariant measures (17 November 2026)

Ten modules added on 17 November 2026 prove the four results that the chapter on non-invariant
measures had taken as outside inputs. Main theorem of each:

| Module | Main declaration(s) |
|---|---|
| `Ergodic/BirkhoffNonErgodic` | `ae_exists_tendsto_birkhoffAverage`, `ae_tendsto_birkhoffAverage_condExp` (Birkhoff without ergodicity, bounded `g`; the limit is the conditional expectation of `g` given `invariants T`) |
| `Ergodic/ErgodicDecomposition` | `exists_ergodicDecomposition` (a Markov kernel `κ` with `μ.bind κ = μ` and `κ x` invariant and ergodic for `μ`-a.e. `x`) |
| `Ergodic/Upcrossing` | `measureReal_upcrossesAtLeast_le` (Bishop's upcrossing inequality for Birkhoff averages), `exists_tendsto_of_forall_not_upcrossesAtLeast` |
| `Measure/Ergodic/ErgodicDecompositionEntropy` | `ae_compProd_localEntropy_eq_ksEntropy_of_ergodicDecomposition`, `ae_compProd_localEntropy_eq_measureEntropy_of_ergodicDecomposition` (Theorem 7.5(b)) |
| `Measure/Ergodic/BrinKatokNonErgodic` | `ae_localEntropy_fst_eq_snd_of_invariant` (Brin–Katok for invariant measures) |
| `Measure/Ergodic/VyuginFrequencies` | `exists_tendsto_frequency_of_mem_randomPoints` (word frequencies converge at random points) |
| `Measure/Ergodic/VyuginGenericity` | `exists_isGenericPoint_of_tendsto_frequency`, `exists_isGenericPoint_of_mem_randomPoints'` (V'yugin's theorem, Remark 7.11) |
| `Measure/Ergodic/FengHuangLowerAux` | `fhLowerWeightedContent`, `fhLower_lowerContent_le_weightedContent` (weighted Bowen content) |
| `Measure/Ergodic/FengHuangLower` | `fhLower_frostman`, `lowerEntropy_le_iSup_measureEntropy'` (Feng–Huang, Bowen entropy) |
| `Measure/Ergodic/FengHuangUpper` | `fhUpper_exists_kernel`, `fhUpper_tree`, `fhUpper_limit`, `upperEntropy_le_iSup_measureEntropy'` (Feng–Huang, packing entropy) |

**Ergodic decomposition, Theorem 7.5(b), non-ergodic Brin–Katok.** `exists_ergodicDecomposition`
takes `κ = condExpKernel μ (invariants T)` (a compact metric space is standard Borel); invariance
of `κ x` is tested on a countable generating algebra, and ergodicity follows from
`ae_tendsto_birkhoffAverage_condExp`. Theorem 7.5(b) is proved by an algorithmic route, without
Jacobs' theorem on the entropy of an ergodic decomposition: Theorem 7.3(a) and the ergodic
Brin–Katok formula `ae_localEntropy_eq_ksEntropy` give `Φ_{κ ω} = (h_ω, h_ω) ≤ Φ_μ`; for the
reverse bound (`ae_compProd_upperLocalEntropy_le_ksEntropy`), at a `μ`-random point `x` the
computable partition of Lemma 2 built for `μ` serves for `κ ω` too, the itinerary of `x` is
generic for the coded component (`ae_isGenericPoint_symbolicCode_of_ergodic`), and block coding
bounds `h̄_μ(T, x) = K̄^A(x, T)` by `h_ω`. Brin–Katok for an invariant `μ` follows by applying
Theorem 7.5(b) to the decomposition with `Q = μ`. The hypothesis `h̄_μ(T) < ∞` of the first
formalization of both statements was dropped.

**V'yugin's theorem.** For a shift-invariant, not necessarily ergodic, `μ` on `ℕ → α` (`α`
finite, first-difference metric) and an oracle admissible for `μ` that computes the symbols of
the ideal points, every `μ`-random point is generic for some shift-invariant probability
measure. This is the non-ergodic statement of Remark 7.11, distinct from the `limsup` half of
(I3) above. Route: Bishop's upcrossing inequality in V'yugin's potential form
(`measureReal_upcrossesAtLeast_le`; V. V. V'yugin, *Ergodic theorems for individual random
sequences*, 1997, and arXiv:2202.13465, §4.2) bounds by `2^{-m}` the measure of the uniformly
c.e. open set of points whose frequency of a word `w` upcrosses `[a, b]` at least `2^m c` times;
this is a `μ`-test, so at a random point every word frequency crosses each rational interval
boundedly often and converges (`exists_tendsto_frequency_of_mem_randomPoints`; the computability
of `μ` is not used). The limits define a shift-invariant probability measure for which `x` is
generic: a cluster point of the empirical measures in the compact space of probability measures,
identified on the clopen cylinders (`exists_isGenericPoint_of_tendsto_frequency`).

**Feng–Huang variational principle, hard halves.** D.-J. Feng and W. Huang, J. Funct. Anal. 263
(2012), Theorems 1.2 and 1.3, for a nonempty compact `K`. Lower (Bowen) half: a weighted Bowen
content, sublinear and dominating the Bowen content through maximal separated nets
(`FengHuangLowerAux`), and a dynamical Frostman lemma (`fhLower_frostman`, by Hahn–Banach and
Riesz–Markov–Kakutani) give a probability measure on `K` whose lower local entropy is at least
`s` everywhere. Upper half, for the chapter's `upperEntropy` (the modified upper capacity
entropy, equal to the packing entropy of Feng–Huang by
`entropy_eq_zeroPotentialPressure_of_nonempty_upper` and `pressureEquivalence_upper`): a kernel
of `K` none of whose nonempty relatively open pieces is thin for the modified upper capacity
(`fhUpper_exists_kernel`), a Cantor tree of `(n, 4ε)`-separated sets with the mass of a node
split equally among its children (`fhUpper_tree`), and a weak-* cluster point of the level
measures (`fhUpper_limit`).

## Jacobs' theorem and the last leaves of the note on non-invariant measures (17–18 November 2026)

Twelve modules, added after the previous section: `CantorPresentation`, `CantorLevinSchnorr`,
`UniversalMeasureWords`, `BernoulliRandom` and `ConformalBallComparison` later on 17 November
2026, the others on 18 November 2026. Main theorem of each:

| Module | Main declaration(s) |
|---|---|
| `Ergodic/Jacobs` | `jacobs_entropyRate_bind`, `jacobs_ksEntropy_bind` (Jacobs' theorem), `jacobs_ksEntropy_eq_lintegral_ergodicDecomposition` |
| `Measure/Ergodic/KSInvariant` | `jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving` (Feng–Huang = Kolmogorov–Sinai for every invariant measure), `jacobs_measureEntropy_bind_eq_lintegral_ksEntropy`, `jacobs_lintegral_entropyLaw_fst`, `jacobs_lintegral_entropyLaw_snd` (Remark 6.7), `jacobs_ksEntropy_bernoulliMixture` (Example 5.3) |
| `Measure/Ergodic/ShiftKSEntropy` | `shiftKS_shiftEntropy_eq_ksEntropy`, `shiftKS_upperOrbitComplexity_le_ksEntropy`, `shiftKS_orbitComplexities_eq_ksEntropy` (Proposition 7.10 in Kolmogorov–Sinai form) |
| `Measure/Ergodic/CantorPresentation` | `cantorPresentation`, `cantorPres_computableIn_symbols`, `cantorPres_isMeasureAdmissible`, `cantorPres_randomPoints_eq`, `cantorPres_map_mem_randomPoints_of_isMartinLofRandom` (the standard computable presentation of Cantor space) |
| `Measure/Ergodic/CantorInstances` | `upperOrbitComplexity_le_shiftEntropy_cantor`, `orbitComplexities_eq_shiftEntropy_cantor`, and the `*_cantor` forms of Remarks 3.4, 6.6, 7.11 |
| `Measure/Ergodic/CantorLevinSchnorr` | `oracleComplexity_cantorPrefix_le_infoBits'`, `infoBits_le_oracleComplexity_cantorPrefix_of_mem_randomPoints'` (Remark 3.4) |
| `Measure/Ergodic/UniversalMeasureWords` | `abs_infoBits_universalMeasure_cylinder_sub_oracleComplexity_le'` (Remark 6.6) |
| `Measure/Ergodic/BernoulliRandom` | `bernRand_ergodic`, `bernRand_tendsto_freq`, `localEntropy_bernoulliMeasure_eq_crossEntropy_of_mem_randomPoints` (Remark 7.2) |
| `Measure/Ergodic/ConformalBallComparison` | `confBall_localBSDimension_fst_eq_localDimension_fst`, `localBSDimension_eq_localDimension_conformal` (Remark 8.5) |
| `Measure/Ergodic/ExampleFiveFiveUpper` | `exists_countable_atomic_random_upperLocalEntropy_eq_one'` (Example 5.5(1)) |
| `Measure/Ergodic/ExampleFiveFiveLower`, `ExampleFiveFiveLowerAux` | `exists_random_lowerLocalEntropy_eq_zero'` (Example 5.5(2)) |

**Jacobs' theorem** (blueprint node **`erg:jacobs`**, cited by `Ergodic/Jacobs` and
`Measure/Ergodic/KSInvariant`). Let `ρ` be a probability measure on a parameter space, `κ` a
Markov kernel whose values `κ ω` are `T`-invariant for `ρ`-almost every `ω`, and
`μ = ρ.bind κ`. Then `h_μ(T, P) = ∫ h_{κ ω}(T, P) dρ(ω)` for every finite measurable partition
(`jacobs_entropyRate_bind`), and on a compact metric space `h_μ(T) = ∫ h_{κ ω}(T) dρ(ω)`
(`jacobs_ksEntropy_bind`; for the ergodic decomposition
`jacobs_ksEntropy_eq_lintegral_ergodicDecomposition`). The inequality `≥` for a partition is
Jensen's inequality for `-t log t`; `≤` quantizes the masses `κ ω (C)` of the cells of `P^N` on
a grid, splits `μ` along the fibres of the quantization and uses subadditivity; for the
Kolmogorov–Sinai entropy, `≥` uses fine partitions (Walters 8.3) and Fatou's lemma. With
Theorem 7.5(b), integrated, this gives `h̲_μ(T) = h̄_μ(T) = h_μ(T)` for every invariant Borel
probability measure on a compact metric space
(`jacobs_measureEntropy_eq_ksEntropy_of_measurePreserving`): the mean of the entropy law in
Remark 6.7 is the Kolmogorov–Sinai entropy, not only, by definition, the Feng–Huang entropy.
Theorem 7.5(b) itself is still proved without Jacobs' theorem (previous section).

**The last leaves.** `CantorPresentation` fixes the presentation of Cantor space by the
eventually-`false` sequences; the metric table, the symbols of the ideal points and the shift are
computable relative to every oracle, measures with computable cylinders are admissible, randomness
for the presentation is randomness for cylinder tests, and causal computable maps preserve
randomness and cylinder computability. On it, `ExampleFiveFiveUpper` and `ExampleFiveFiveLower`
carry out the two constructions of Example 5.5 from a left-c.e. random real. `CantorLevinSchnorr`
proves both directions of the Levin–Schnorr form of Remark 3.4 (the incompressibility direction
from the word-level bound `exists_infoBits_le_wordComplexity_add` of `HoyrupBasic`, which has
`O(1)`; the statement keeps the note's `O(log n)`); `UniversalMeasureWords` compares
`-log₂ m^A[w]` with `K^A(w)` (Remark 6.6); `BernoulliRandom` proves the ergodicity of Bernoulli
shifts and an effective strong law at every `ν_q`-random point, with no hypothesis on the ideal
points, hence Remark 7.2 at every random point; `ConformalBallComparison` proves the comparison of
Remark 8.5 for every measure, from `ballInclusion` and `nonmonotoneScaleSampling` of
`PointToSet/Conformal/Distortion/DistortionModuli.lean`. The primed declarations above are the
proofs; the unprimed statements are in the chapter (`RemarksShift.lean`, `ExampleFiveFive.lean`).

## Effect on the chapter on non-invariant measures

`ae_localEntropy_eq_of_ergodic` (Remark 6.7, previously an open leaf: Brin–Katok for ergodic
measures) is now proved from `ae_localEntropy_eq_measureEntropy_of_ergodic`, and its hypothesis
`h̄_μ(T) < ∞` was dropped, as were those of `entropyLaw_eq_dirac_of_ergodic` and
`entropyLaw_sum_ergodic`. All three are now unconditional (Brin–Katok for ergodic measures with
the Kolmogorov–Sinai entropy, by an algorithmic proof). Proposition 7.10 is proved as well (see
above). Since 17 November 2026 the chapter has no outside input left: Theorem 7.5(b)
(`ae_compProd_localEntropy_eq_of_ergodicDecomposition`), non-ergodic Brin–Katok
(`ae_localEntropy_fst_eq_snd_of_measurePreserving`), V'yugin's theorem
(`exists_isGenericPoint_of_mem_randomPoints`) and the Feng–Huang leaves
(`lowerEntropy_le_iSup_measureEntropy`, `upperEntropy_le_iSup_measureEntropy`) are proved from
the modules of the 17 November section. Since 18 November 2026 the chapter has no `sorry` at
all: the last 7 leaves (Example 5.5 and Remarks 3.4, 6.6, 7.2, 8.5) are proved by the modules of
the previous section (see `entropy_noninvariant_blueprint.md`).
