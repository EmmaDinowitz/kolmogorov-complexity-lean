# Blueprint

Node-by-node map from mathematical statements to Lean declarations, following the project's
`CLAUDE.md` (sections 3 and 5). The chapters formalized before this file existed keep their own
blueprints (`point_to_set_blueprint.md`, `entropy_noninvariant_blueprint.md`,
`split_precision_blueprint.md`, `crs_random_strings_blueprint.md`, `geodesic/`); they will be
merged here during the planned reorganization.

## 1. Conventions

* Paths are relative to `KolmogorovMathlib/`; namespaces are abbreviated by dropping the prefix
  `Kolmogorov.`. `PointToSet.oracleJoin` keeps its prefix.
* Marks: **⚠** the source's claim is false as printed and a counterexample is proved; **✎** the
  statement is corrected or repaired (hypotheses, indexing or scope differ from the source);
  **◇** the node is realized by a differently named or differently shaped declaration. No mark
  means a faithful rendering.
* "Reviewed" is filled in by the author only.
* Types: measures are `MeasureTheory.Measure CantorSeq`, measures of sets are `ℝ≥0∞`, the test
  bound `2^{-n}` is `dyadicValue 1 n`. Oracles are `Set ℕ`, used through `charOracle`; a
  sequence `x` is used as the oracle `seqOracle x`.
* Chapters: van Lambalgen's theorem (`vl:*`), section 3.

## 2. Main theorems

| Label | Node | Declaration | File |
|---|---|---|---|
| van Lambalgen's theorem | `vl:main` | `isMartinLofRandomIn_cantorJoin_iff` | `AlgorithmicRandomness/VanLambalgen/MainResults.lean` |
| coordinates exchanged | `vl:symm` | `isMartinLofRandomIn_cantorJoin_iff_swap` | same |
| mutual relative randomness | `vl:mutual` | `isMartinLofRandomIn_cantorJoin_iff_mutual` | same |
| uniform measure, no oracle | `vl:uniform` | `isMartinLofRandom_cantorJoin_uniformMeasure_iff` | same |
| non-vacuousness | `vl:nonvacuous` | `exists_isMartinLofRandomIn_cantorJoin` | same |
| countable products | `vl:countable` | `IsMartinLofRandomIn.coordinate_of_cantorPiJoin` | same |
| countable, earlier coordinates | `vl:countable-below` | `IsMartinLofRandomIn.coordinate_of_cantorPiJoin_below` | same |
| countable, non-vacuousness | `vl:countable-nonvacuous` | `exists_isMartinLofRandomIn_cantorPiJoin` | same |

## 3. van Lambalgen's theorem (`vl:*`)

Source: [vanLambalgen1987]; textbook form [Nies2009, §3.4]. The formalization proves the theorem
for a finite measure `μ` (not necessarily computable: blind randomness) and a measure `ν`
computable relative to the oracle `A`.

### Definitions (`AlgorithmicRandomness/Relative/Defs.lean`, `VanLambalgen/Defs.lean`; protected)

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:seq-oracle` | A sequence read as an oracle: `{n | x n = true}`. | `seqOracle` | | |
| `vl:effective-open-in` | Uniformly effectively open relative to `A`: cylinders enumerated by one function computable in `A`. | `IsUniformlyEffectiveOpenIn` | | |
| `vl:computable-measure-in` | Cylinder masses approximable in `A` with two-sided error `2^{-s}`; computable measures are relatively computable, relatively computable measures are finite. | `IsComputableCantorMeasureIn`; `IsComputableMeasure.isComputableCantorMeasureIn`, `IsComputableCantorMeasureIn.isFiniteMeasure` | | |
| `vl:test-in` | Martin-Löf test relative to `A`. | `IsMartinLofTestIn` | | |
| `vl:random-in` | Martin-Löf randomness relative to `A` (blind when `μ` is not `A`-computable). | `IsMartinLofRandomIn` | | |
| `vl:join` | Interleaving `x ⊕ y`: `x` on even positions, `y` on odd; every sequence is one. | `cantorJoin`; `exists_cantorJoin_eq` | | |
| `vl:join-measure` | `joinMeasure μ ν`: the image of `μ.prod ν` under interleaving; its total mass. | `joinMeasure`; `joinMeasure_univ` | | |

### Basic facts (`AlgorithmicRandomness/Relative/Basic.lean`, `VanLambalgen/Join.lean`)

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:random-in-anti` | If `A ≤_T B`, random relative to `B` implies random relative to `A`; `∅ ⊕ B` may replace `B`. | `IsMartinLofRandomIn.mono_oracle`; `isMartinLofRandomIn_oracleJoin_empty_left` | | |
| `vl:random-in-empty` | Randomness relative to `∅` is `IsMartinLofRandom`. | `isMartinLofRandomIn_empty_iff` | | |
| `vl:ae-random` | For every measure and oracle, the non-random sequences are null. | `measure_setOf_not_isMartinLofRandomIn` | | |
| `vl:join-oracle` | `seqOracle (x ⊕ y) = oracleJoin (seqOracle x) (seqOracle y)`. | `seqOracle_cantorJoin` | | |
| `vl:join-uniform` | `joinMeasure uniformMeasure uniformMeasure = uniformMeasure`. | `joinMeasure_uniformMeasure` | | |
| `vl:swap` | `x ⊕ y` random for `joinMeasure μ ν` iff `y ⊕ x` random for `joinMeasure ν μ` (s-finite factors). | `isMartinLofRandomIn_joinMeasure_swap` | | |
| `vl:pullback` | Pulling a family that is uniformly effectively open relative to `A` back along a map whose cylinder preimages are computably enumerated unions of cylinders (in particular precomposition with a primitive recursive index map) keeps it effectively open relative to `A`; its members are measurable. `Relative/Pullback.lean`. | `IsUniformlyEffectiveOpenIn.preimage`; `IsUniformlyEffectiveOpenIn.preimage_precomp`, `IsUniformlyEffectiveOpenIn.measurableSet` | | |

### Machinery for the hard directions (`VanLambalgen/Halves.lean`, `VanLambalgen/OracleUniform/`)

The definitions of these nodes are in the protected file `VanLambalgen/Auxiliary/Defs.lean`; the
lemmas are in the files named in each row.

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:halves` | The even and odd halves of sequences and strings; the halves of `x ⊕ y` are `x` and `y`; a cylinder is the product of the cylinders of its halves. Definitions in `Auxiliary/Defs.lean`, lemmas in `Halves.lean`. | `cantorEvens`, `cantorOdds`, `evenBits`, `oddBits`; `cantorEvens_cantorJoin`, `cantorOdds_cantorJoin`, `mem_cantorCylinder_iff_halves`, `evenBits_cantorPrefix`, `oddBits_cantorPrefix`, `primrec_evenBits`, `primrec_oddBits` | | |
| `vl:joint-set` | `jointSet T = {z ⊕ y \| y ∈ T z}`; every set is the joint set of its sections; interleaving is measurable. Definition in `Auxiliary/Defs.lean`, lemmas in `Halves.lean`. | `jointSet`; `cantorJoin_mem_jointSet`, `jointSet_sections`, `measurable_cantorJoin` | | |
| `vl:joint-fubini` | `joinMeasure μ ν (jointSet T) = ∫⁻ z, ν (T z) ∂μ` for a measurable joint set (`ν` s-finite). `Halves.lean`. | `joinMeasure_jointSet` | | |
| `vl:oracle-uniform` | Oracle-uniform families: listings `g σ n i` over oracle prefixes `σ`, computable in `A`; their joint sets are effectively open relative to `A`, their member at `x` is effectively open relative to `A ⊕ x`. Definitions in `Auxiliary/Defs.lean`, lemmas in `OracleUniform/Basic.lean`. | `IsOracleUniformIn`, `uniformEnum`, `uniformFamily`; `IsOracleUniformIn.isUniformlyEffectiveOpenIn_jointSet`, `IsOracleUniformIn.isUniformlyEffectiveOpenIn_uniformFamily`, `IsOracleUniformIn.reindex`, `computableIn_list_range_map` | | |
| `vl:sections` | The sections of an effectively open set relative to `A` form an oracle-uniform family relative to `A`. Definition in `Auxiliary/Defs.lean`, lemmas in `OracleUniform/Basic.lean`. | `sectionEnum`; `uniformFamily_sectionEnum`, `isOracleUniformIn_sectionEnum` | | |
| `vl:use-principle` | Every family effectively open relative to `A ⊕ x` is the member at `x` of an oracle-uniform family relative to `A`. `OracleUniform/UsePrinciple.lean`. | `exists_isOracleUniformIn_uniformFamily_eq` | | |
| `vl:uniform-trim` | For `ν` computable relative to `A`, trimming an oracle-uniform family gives an oracle-uniform family whose level-`L` member has `ν`-measure at most `2^{-L}` at every oracle, and equals the original outside the discard set. Definitions (`trimUniform`, namespace `TrimUniform`) in `Auxiliary/Defs.lean`, lemmas in `OracleUniform/Trim.lean`. | `trimUniform`; `isOracleUniformIn_trimUniform`, `measure_uniformFamily_trimUniform_le`, `uniformFamily_trimUniform_of_not_mem` | | |
| `vl:discard` | The oracles at which trimming discards something form a family effectively open relative to `A`, and each of them has `ν(T z n) > 2^{-(L+2)}`. Definition in `Auxiliary/Defs.lean`, lemmas in `OracleUniform/Trim.lean`. | `discardSet`; `isUniformlyEffectiveOpenIn_discardSet`, `lt_measure_of_mem_discardSet` | | |

### The three directions (`AlgorithmicRandomness/VanLambalgen/Directions.lean`)

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:fst` | `x ⊕ y` random ⇒ `x` random (`ν` finite). `Directions/Left.lean`. | `IsMartinLofRandomIn.left_of_cantorJoin` | | |
| `vl:snd` | `x ⊕ y` random ⇒ `y` random relative to `A ⊕ x` (`μ` finite, `ν` `A`-computable). Use principle, uniform trimming, Fubini. `Directions/Right.lean`. | `IsMartinLofRandomIn.right_of_cantorJoin` | | |
| `vl:converse` | `x` random and `y` random relative to `A ⊕ x` ⇒ `x ⊕ y` random (`ν` `A`-computable). The discard sets of the trimmed sections are the Markov sets. `Directions/Converse.lean`. | `IsMartinLofRandomIn.cantorJoin` | | |

### Main results (`AlgorithmicRandomness/VanLambalgen/MainResults.lean`; protected)

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:main` | `x ⊕ y` random for `joinMeasure μ ν` relative to `A` ⟺ `x` random for `μ` relative to `A` and `y` random for `ν` relative to `A ⊕ x` (`μ` finite, `ν` `A`-computable). | `isMartinLofRandomIn_cantorJoin_iff` | ✎ | |
| `vl:symm` | The same with the coordinates exchanged (`μ` `A`-computable, `ν` finite). | `isMartinLofRandomIn_cantorJoin_iff_swap` | | |
| `vl:mutual` | For `A`-computable `μ`, `ν`: `x ⊕ y` random ⟺ each coordinate random relative to `A` joined with the other. | `isMartinLofRandomIn_cantorJoin_iff_mutual` | | |
| `vl:uniform` | Textbook form: `x ⊕ y` uniformly random ⟺ `x` random and `y` random relative to `x`. | `isMartinLofRandom_cantorJoin_uniformMeasure_iff` | | |
| `vl:nonvacuous` | For nonzero `μ`, `ν` some pair satisfies both sides of `vl:main`. | `exists_isMartinLofRandomIn_cantorJoin` | | |

The mark ✎ on `vl:main` records a change of scope relative to the textbook statement: it is
stated for an arbitrary oracle, an arbitrary finite measure `μ` (blind randomness) and an
`A`-computable `ν`, rather than for two computable probability measures. The textbook statement is
`vl:uniform`.

### Countable products (`VanLambalgen/Countable/`; headline results in `MainResults.lean`)

Phase 2. For probability measures `μ j` (so that `Measure.infinitePi μ` is their product), only the
direction from the infinite join to its coordinates holds; the countable converse is false (see
below) and is not formalized.

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:pi-join` | The infinite join `⊕ⱼ xⱼ` (Cantor pairing), the joins of all coordinates but one and of the coordinates below an index; every sequence is an infinite join. `Countable/Defs.lean` (protected), `Countable/Split.lean`. | `cantorPiJoin`, `cantorPiJoinExcept`, `cantorPiJoinBelow`; `exists_cantorPiJoin_eq` | | |
| `vl:pi-join-measure` | `piJoinMeasure μ`: `Measure.infinitePi μ` carried by the infinite join; a probability measure for probability `μ j`. | `piJoinMeasure`; `isProbabilityMeasure_piJoinMeasure` | | |
| `vl:pi-split` | `⊕ⱼ xⱼ` is random for `piJoinMeasure μ` iff `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` is random for the joined product of the other measures' product with `μ i`. | `skipIndex`, `cantorPiJoinSkip`; `isMartinLofRandomIn_cantorPiJoin_iff_split` | | |
| `vl:permute` | Randomness is invariant under precomposition with a primitive recursive map of positions `π` that has a primitive recursive right inverse: `z` is random for `ν` iff `z ∘ π` is random for the image of `ν` under `w ↦ w ∘ π`. No finiteness of `ν`. `Relative/Pullback.lean`; also gives the swap `vl:swap`. | `isMartinLofRandomIn_map_precomp_iff` | | |
| `vl:pi-oracles` | The reindexed and the blanked oracles of the other coordinates give the same relative randomness; the earlier coordinates reduce to the other coordinates. | `isMartinLofRandomIn_oracleJoin_cantorPiJoinSkip_iff`, `charOracle_oracleJoin_cantorPiJoinBelow_le` | | |
| `vl:countable` | `⊕ⱼ xⱼ` random for `piJoinMeasure μ` relative to `A` and `μ i` computable relative to `A` ⇒ `xᵢ` random for `μ i` relative to `A ⊕ (⊕_{j ≠ i} xⱼ)`. `MainResults.lean`. | `IsMartinLofRandomIn.coordinate_of_cantorPiJoin` | | |
| `vl:countable-below` | The same relative to `A ⊕ (⊕_{j < i} xⱼ)`. | `IsMartinLofRandomIn.coordinate_of_cantorPiJoin_below` | | |
| `vl:countable-nonvacuous` | For probability `μ j` some infinite join is random relative to `A`. | `exists_isMartinLofRandomIn_cantorPiJoin` | | |

Not formalized: the countable converse ("each `xᵢ` random relative to the earlier coordinates ⇒
`⊕ⱼ xⱼ` random"). It is false: with `(zⱼ)` the columns of a random sequence and `xⱼ = 0ʲ zⱼ`, each
`xⱼ` is random relative to the earlier coordinates, but `⊕ⱼ xⱼ` has forced zeros on the
computable set of positions `pair j k`, `k < j`, a Martin-Löf null set for the product.

### Planned (not yet stated)

* Phase 3: transfer to presented metric spaces through almost-decidable balls (Hoyrup–Rojas),
  for finite measures with `A`-computable total mass.

## 4. Corrections

None so far.

## References

See `docs/references.bib`: `vanLambalgen1987`, `Nies2009`, `HoyrupRojas2009`.
