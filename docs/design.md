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

## 2026-11-12 — proofs of `vl:snd` and `vl:converse`

* **Oracle-uniform families** (`OracleUniform/Basic.lean`) are listings `g σ n i` over finite
  prefixes `σ` of the oracle sequence, computable in `A`; `g` need not be monotone in `σ`. The
  member at `z` lists `g (z↾k) n i` at index `⟨k, i⟩`. Rejected: a monotone c.e. relation on
  triples `(σ, n, τ)`, which needs a separate monotonization step.
* **Use principle** via `PointToSet.oracleStage_universal`: stage `t` of the universal oracle
  machine reads only queries below `t` (`Nat.unpair_left_le`), so it can be re-run on the prefix
  of `A ⊕ σ`; a private plain-computable copy of the stage function (`stageOnPrefix`) does this.
  `Oracle/FinitePrefix.lean`'s `exists_exact_string_operator` was not needed.
* **Uniform trimming** reuses `disjEnum` (`Disjointify.lean`) and `trimEnum` (`Trim.lean`)
  unchanged, so their measure lemmas apply. Both are local (entry `j` depends only on entries
  `≤ j`, hence on `z↾j`). Disjointifying first makes the sum of the masses equal the measure of
  the union, so measures of finite unions never need to be approximated.
* **The discard set does double duty.** In `vl:snd` it shows nothing is trimmed at `x`; in
  `vl:converse` it is the Markov set: `μ(D_L) ≤ 2^{-(L+1)}` at section level `2L + 3`, and
  `V_k = ⋃_L D_{L+k+1}` is the test that `x` avoids.
* **Pitfall: `whnf` timeouts.** `have h : ComputableIn O (fun x ↦ someDef …) := ComputableIn.comp
  h1 h2` makes the unifier unfold `someDef` and time out. Compose without an expected type and
  close with `.of_eq fun _ ↦ rfl`. Also: `cond_true` is deprecated (`Bool.cond_true`); `List`'s
  `==` is not the instance `Primrec.beq` expects (use `decide (a = b)` with `Primrec.eq.decide`);
  definitions with a classical `if k ∈ A` must be `noncomputable`.
* **Mechanical-cut gate.** Two private helpers in `OracleUniform/Trim.lean` whose index-bound
  hypotheses were discharged by `omega` at their single call site were inlined into their callers.
* **Layout of the proof definitions** (resolved later the same day, see below).

## 2026-11-12 — phase 2: countable products

* **Only the direction from the join to its coordinates.** The countable converse is false
  (columns `xⱼ = 0ʲ zⱼ` of a random sequence: each coordinate random relative to the earlier ones,
  the join in a computable null set), so it is recorded as not formalized, not stated.
* **Reduction to the binary theorem.** Splitting coordinate `i` off is precomposition with the
  primitive recursive position map `splitIndex i` (inverse `mergeIndex i`), proved
  randomness-preserving once in general (`isMartinLofRandomIn_map_precomp_iff`, `vl:permute`).
  The binary `vl:snd` then gives randomness relative to the reindexed other coordinates, and
  `vl:pi-oracles` converts to the blanked form. Only `μ i` needs to be computable relative to `A`.
* **Splitting the product measure.** Mathlib has no `infinitePi` over a sum or `Option` index type.
  `infinitePi μ` is shown to be the image of `(infinitePi (μ ∘ skipIndex i)).prod (μ i)` under the
  coordinate-insertion map by `Measure.eq_infinitePi` on boxes, with the box preimage written over
  `(s.erase i).image unskip` (avoids injectivity side terms), then `Finset.prod_image`,
  `Finset.prod_erase_mul`. `Measure.eq_infinitePi μ` and `Measure.infinitePi_pi _` take `μ`
  explicitly; `Measurable.prodMap` is the current name; there is no `isProbabilityMeasure_map`
  lemma (use `inferInstanceAs`).
* **Oracle reductions with constant answers.** Queries answered by `false` use
  `PartrecIn.cond_some` with `ComputableIn.const 0`, then `PartrecIn.of_eq`, combined with
  `oracle_joins_least` / `oracle_joins`.
* **Dedup.** `measurable_cantorJoin` (public, `Halves.lean`) replaces three private copies in
  `Join.lean`, `Directions/Left.lean` and `Countable/Split.lean`.
* **Possible later cleanup.** The swap of `Join.lean` is an instance of `vl:permute` (an
  involution); its proof could be shortened by moving `vl:permute` to `Relative/Pullback.lean`.

## 2026-11-12 — layout cleanup

* **Proof definitions in a protected file.** At the author's request the definitions the proofs
  use (`cantorEvens`, `cantorOdds`, `evenBits`, `oddBits`, `jointSet`, `IsOracleUniformIn`,
  `uniformEnum`, `uniformFamily`, `sectionEnum`, `trimUniform`, `discardSet`) moved to
  `VanLambalgen/Auxiliary/Defs.lean`. The finite-list helpers of `trimUniform` were private in
  `OracleUniform/Trim.lean`; a definition in another file cannot use private names, so they are
  public, in the namespace `Kolmogorov.TrimUniform` to keep generic names (`listEnum`,
  `localDisj`, …) out of the main namespace. Purely proof-local encodings (stage decoders,
  index maps such as `swapIndex`, `splitIndex`) stay private next to their lemmas.
* **`vl:permute` moved to `Relative/Pullback.lean`**, next to `preimage_precomp`, and the swap
  `vl:swap` is now its instance with the self-inverse `swapIndex` (the hand-written pullback of
  tests in `Join.lean` is gone).
