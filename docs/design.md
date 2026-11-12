# Design log

Dated entries: design decisions (with the alternatives rejected), Lean or Mathlib pitfalls that
cost time, numerical checks, abandoned approaches. Read at the start of every session.

## 2026-11-12 — van Lambalgen's theorem: setting and scope

* **Setting: Cantor space.** Rejected: proving the theorem directly on presented metric spaces
  (`PointToSet.randomPoints`). There a point is not an oracle (only its Cauchy names are, and
  names of one point can have different Turing degrees), and the oracle-uniform trimming needs
  basic sets of computable measure, i.e. the Hoyrup–Rojas almost-decidable balls. On Cantor
  space a sequence is its own oracle and cylinders are clopen with computable mass. The
  metric-space version is planned as phase 3, by transfer along the itinerary map of an
  almost-decidable basis, for finite measures with `A`-computable total mass.
* **New relativized notions on Cantor space** (`AlgorithmicRandomness/Relative/Defs.lean`) rather
  than a presentation of Cantor space feeding `PointToSet.randomPoints`: the unrelativized
  notions of the library are cylinder-based, and the bridge `vl:random-in-empty` connects them.
* **Name `IsComputableCantorMeasureIn`**: `IsComputableMeasureIn` is taken by
  `PointToSet.IsComputableMeasureIn` (presented spaces, balls).
* **Hypotheses are the ones each direction uses.** Mathlib's `Measure.prod_prod` and
  `Measure.prod_apply` need `[SFinite ν]` only. `vl:fst` uses `ν` finite; `vl:converse` uses `ν`
  `A`-computable; `vl:snd` uses in addition `μ` finite (the test for pairs has measure
  `∫ ν(T^z_n) dμ ≤ μ(univ) 2^{-n}`). `μ` is never assumed computable, so for non-computable `μ`
  the statements are about blind (Hippocratic) randomness; the author chose this generality.
  The symmetric forms need `μ` `A`-computable.
* **Oracle of a sequence**: `seqOracle x = {n | x n = true}`; `A ⊕ x` is
  `PointToSet.oracleJoin A (seqOracle x)`. The interleaving `cantorJoin` uses the same parity
  convention (first argument on even positions).
* **Sampling for the Lyapunov paper** does not need van Lambalgen: the points can be sampled one
  at a time, each random relative to the join of the earlier ones. van Lambalgen is formalized
  because it is generally useful.

## 2026-11-12 — build setup

* Worktree `C:\Users\emmad\code\kolmogorov-vanlambalgen`, branch `van-lambalgen` off
  `measure-chapter` (`cedfa17`). `.lake/packages` is a junction to `kqw/.lake/packages` (same
  Mathlib commit `56a0058`); `.lake/build` was copied from a build of `0e93f21`, whose
  `AlgorithmicRandomness/` and `Oracle/` files are identical to `cedfa17`'s.
* Run Lean with `LEAN_NUM_THREADS=3` on the 16 GB machine. A single `lake env lean` on a file
  importing `MartinLof` and `Oracle.Joins` takes about five minutes, mostly import loading.

## 2026-11-12 — proofs of the basic facts, the interleaving lemmas and `vl:fst`

* `ComputableIn₂ {charOracle ∅} f ↔ Computable₂ f` comes from `RecursiveIn.partrec_of_oracle`
  with `Partrec.const'`, since `charOracle ∅ = fun _ ↦ Part.some 0`.
* Countability of the tests relative to `A` (for `vl:ae-random`) goes through
  `PointToSet.oracleStage_universal` (`Oracle/Universal/Enumeration.lean`): every enumeration
  computable in `A` is matched by an index of the universal oracle machine.
* With an arbitrary, possibly infinite, measure the bounds `μ(U n) ≤ 2^{-n}` still give
  `μ(⋂ U n) = 0`; no finiteness is needed for `vl:ae-random`.
* Pullback (`Relative/Pullback.lean`) takes cylinder preimages as an enumeration
  `φ : BitString → ℕ → Option BitString` (a countable union of cylinders), not a finite list:
  more general and easier to compute with. For precomposition `z ↦ z ∘ π` the index map `π` must
  be `Primrec` (the cover tests list equality; Mathlib has `Primrec.list_map` but no
  `Computable.list_map`). The swap is precomposition with `n ↦ if n even then n + 1 else n - 1`,
  the even part precomposition with `n ↦ 2 n`.
* Pitfalls in this Mathlib: `measurable_pi_lambda` is deprecated (use `Measurable.of_eval`);
  `if_pos`/`if_neg`, `Set.mem_setOf_eq` and `push_neg` are deprecated (use `↓reduceIte` in
  `simp only`, `Set.mem_ofPred_eq`, `push Not`); in `rw [← Measure.prod_swap]` give
  `(μ := μ) (ν := ν)` explicitly; `Part.bind (Encodable.decode n) …` needs the explicit
  coercion `((decode n : Option _) : Part _)`; after `refine ⟨fun n i ↦ …, _, fun n ↦ ?_⟩` the goal
  is a beta-redex, so `dsimp only` before rewriting.
* Small duplication: the measurability of the join map is proved privately in `Join.lean` and
  inline in `Directions/Left.lean`, which does not import `Join.lean`.
