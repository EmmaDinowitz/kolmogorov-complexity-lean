# Formalized Algorithmic Information Theory in Lean 4

This repository contains a Lean 4 formalization of algorithmic information theory,
built on Mathlib.

The main references are Alexander Shen, Vladimir A. Uspensky, and Nikolai Vereshchagin,
[*Kolmogorov Complexity and Algorithmic Randomness*](https://www.lirmm.fr/~ashen/kolmbook-eng-scan.pdf)
(SUV), and Nikolai Vereshchagin and Alexander Shen,
[*Algorithmic statistics: forty years later*](https://arxiv.org/abs/1607.08077).

The development is based on Mathlib's computability infrastructure. Decompressors are represented as partial functions, finite objects are represented by bitstrings, and most theorem statements are phrased up to the additive or logarithmic slack terms natural in Kolmogorov-complexity arguments.

## What Is Formalized

- **The SUV book:** selected results on plain, prefix and monotone complexity,
  algorithmic probability and randomness, Shannon entropy, information inequalities,
  common information and multisource information theory.
- **Algorithmic statistics:** finite-set and distribution models, stochasticity
  profiles, restricted descriptions and strong sufficient statistics, following
  the Vereshchagin-Shen survey.
- **Incompleteness:** Chaitin-style and
  [Kritchman-Raz-style results](https://arxiv.org/abs/1011.4974), using abstract
  formal-system interfaces rather than a concrete arithmetic system.
- **Further developments:** Solomonoff induction, Solomonoff prediction of selected
  bits, the negative answer to Shen's question on the a priori probability of a prefix,
  stopping complexity, and the exact realisation of `min(K, F)` for an entropy function `F`
  by a prefix machine (Allender-Friedman-Gasarch, Claim 1), and the Allender-Friedman-Gasarch
  theorem that a decidable set polynomial-time reducible to the `K_U`-random strings for
  every optimal prefix machine `U` lies in `EXPSPACE` (resource-bounded machines, complexity
  classes and the game construction in `KolmogorovMathlib/RandomStrings/`).
- **C-random strings:** the theorem of Milovanov, *Limit on the Computational Power
  of C-Random Strings* (FOCS 2026), that some optimal plain decompressor `U` has a
  cumulative complexity oracle and a set of `C_U`-random strings neither of which computes
  the halting language in polynomial time
  (`Kolmogorov.Milovanov.exists_optimal_native_halting_oracle_separation` in
  `KolmogorovMathlib/RandomStrings/Plain/`).
- **Point-to-set principles in dynamical systems:** Dinowitz's characterizations of
  topological pressure, Barreira-Schmeling dimension and, for conformal systems, Hausdorff
  and packing dimension as minima over oracles of suprema of pointwise Kolmogorov-complexity
  quantities, and the Bowen equations, following a corrected blueprint with counterexamples
  to the printed claims that fail (`Kolmogorov.PointToSet.lowerPressure_pointToSet`,
  `bsPointToSet`, `dimensionTheorem` in `KolmogorovMathlib/PointToSet/`, built on the oracle
  prefix complexity of `KolmogorovMathlib/Oracle/`).
- **Mutual information at split precisions:** for points of presented metric spaces
  observed at two unrelated precisions `r`, `s`, the mutual information of the two balls
  equals that of their `K`-minimizers up to `O(log r) + O(log s)`, and satisfies symmetry of
  information `I_{r,s}(x : y) = K_r(x) + K_s(y) - K_{r,s}(x, y) + O(log r) + O(log s)`, with
  the tuple versions and the normalized limits along comparably divergent precisions
  (`KolmogorovMathlib/PointToSet/SplitPrecision/`, blueprint `docs/split_precision_blueprint.md`),
  on top of the conditional calculus of the oracle prefix complexity `K^A`, including symmetry
  of information for every oracle (`KolmogorovMathlib/Oracle/PrefixComplexity/`).
- **Entropy of non-invariant measures:** for a Borel probability measure `μ`, not assumed
  invariant, and an oracle computing the system and the measure, the lower and upper orbit
  complexities are at most the Brin–Katok local entropies of `μ` at every point and equal
  them at every Martin-Löf random point, and likewise for pointwise pressure and BS dimension;
  Billingsley-type bounds and dual principles `h(Z) = min_μ sup_{x ∈ Z} h_μ(x)` for arbitrary
  sets; the essential bounds of the local entropies as suprema and infima over random points;
  information rates along Bowen balls and their comparison with the Feng–Huang entropies; the
  domination lemma and the entropy law under absolute continuity, convex combinations and
  integral decompositions, including ergodic decompositions; the Feng–Huang variational
  principles for the Bowen and packing entropies of compact sets; Brin–Katok for invariant
  measures, whose Feng–Huang entropy is their Kolmogorov–Sinai entropy (by Jacobs' theorem);
  V'yugin's theorem that random points of an invariant measure on a shift are generic; examples
  on shifts, including the constructions showing that Martin-Löf randomness is not enough for the
  essential bounds; no `sorry`
  (`KolmogorovMathlib/PointToSet/Measure/`, blueprint `docs/entropy_noninvariant_blueprint.md`,
  which also lists the sentences of the note that are not stated).
- **Orbit complexity of Martin-Löf random points equals entropy:** on a compact space, for a
  computable ergodic invariant measure, both orbit complexities of every Martin-Löf random
  point equal the Kolmogorov–Sinai entropy, which is defined here together with Walters 8.3,
  the maximal ergodic inequality, Birkhoff's theorem (also without ergodicity), the ergodic
  decomposition, Bishop's upcrossing inequality, null-sphere radii, computable partitions and
  symbolic coding, and Hoyrup's theorem (the lower half of the effective
  Shannon–McMillan–Breiman theorem, relativized), with effective Poincaré recurrence; the same
  modules prove Proposition 7.10, Theorem 7.5(b), Brin–Katok, V'yugin's theorem, the hard
  half of the Feng–Huang variational principle, Jacobs' theorem on the entropy of an integral
  decomposition and the last leaves of the note on non-invariant measures; no `sorry`
  (`KolmogorovMathlib/Ergodic/`, `KolmogorovMathlib/PointToSet/Measure/Ergodic/`, blueprint
  `docs/ml_random_orbit_complexity_blueprint.md`).
- **New strong-merging results:** the square-root merger of two strong sufficient
  statistics, its matching obstruction and the questions of survey Section 7.9.

The [detailed overview](docs/RESULTS.md) lists the main theorems and their modules.
The [SUV coverage table](docs/SUV_COVERAGE.md) records exactly which book items
are covered and which are not.

## Build

Install Lean through `elan`, then fetch the Mathlib cache and build the exported library target:

```bash
lake exe cache get
lake build KolmogorovMathlib
```

For the default package build — the library together with the counterexample
library — run:

```bash
lake build
```

`bash scripts/audit.sh` is the completion gate (forbidden constructs, `sorry` scan,
build, warning gate, co-import smoke test, axiom sweep, tactic smoke tests).

The [SUV coverage table](docs/SUV_COVERAGE.md) maps book items to theorems and
is regenerated by `scripts/gen_suv_coverage.py`.

The HTML documentation is built from the side package `docbuild/`, which is the
only place `doc-gen4` is required, at a revision pinned to this repository's
Lean release:

```bash
cd docbuild
lake update doc-gen4
lake build KolmogorovMathlib:docs KolmogorovCounterexamples:docs   # writes .lake/build/doc
```

`.github/workflows/ci.yml` runs the build, the audit, the test scripts under
`scripts/tests/` and the documentation build; `scripts/ci_local.sh` runs the
same steps locally, and the workflow calls that script so the two cannot drift
apart.

The library has a single build root, `KolmogorovMathlib`, which imports every module
of the library, directly or through other modules: the root imports the maximal modules
of the topic directories itself, and `KolmogorovMathlib/Extras.lean`, which the root also
imports, collects the side modules outside the main development line (alternative
developments, spare interfaces and side results), so that they stay in the build.
`KolmogorovCounterexamples` is a
second root, deliberately not imported by the library, and the release check builds
it too.

This branch is pinned to Lean `v4.35.0` and the matching Mathlib ecosystem.

## Branches

`main` is the development branch and is pinned to Lean `v4.35.0` together with
the matching Mathlib ecosystem. Historical branches preserve earlier Lean releases.

## Project Layout

The [module tree and project layout](docs/RESULTS.md#project-layout) are included
with the detailed overview.

## Lake Metadata

The Lake package is named `kolmogorov_complexity`; the Lean library targets are
`KolmogorovMathlib` and `KolmogorovCounterexamples`. The Mathlib dependency is pinned in `lakefile.toml` and
`lake-manifest.json` to the Lean `v4.35.0` ecosystem.
