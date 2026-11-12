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

### The three directions (`AlgorithmicRandomness/VanLambalgen/Directions.lean`)

| Node | Claim | Declaration | Mark | Reviewed |
|---|---|---|---|---|
| `vl:fst` | `x ⊕ y` random ⇒ `x` random (`ν` finite). | `IsMartinLofRandomIn.left_of_cantorJoin` | | |
| `vl:snd` | `x ⊕ y` random ⇒ `y` random relative to `A ⊕ x` (`μ` finite, `ν` `A`-computable). | `IsMartinLofRandomIn.right_of_cantorJoin` | | |
| `vl:converse` | `x` random and `y` random relative to `A ⊕ x` ⇒ `x ⊕ y` random (`ν` `A`-computable). | `IsMartinLofRandomIn.cantorJoin` | | |

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

### Planned (not yet stated)

* `vl:countable` (phase 2): for uniformly `A`-computable measures `μ_i` and `x` random for their
  product, each `x_i` is random relative to `A` joined with all `x_j`, `j ≠ i`.
* Phase 3: transfer to presented metric spaces through almost-decidable balls (Hoyrup–Rojas),
  for finite measures with `A`-computable total mass.

## 4. Corrections

None so far.

## References

See `docs/references.bib`: `vanLambalgen1987`, `Nies2009`, `HoyrupRojas2009`.
