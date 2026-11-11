# Notes on Chapter C (`Geodesic/EffectiveData.lean`)

Status (wave 2): zero errors against the fresh Chapter B olean. Fields `Kplaque_cc`, `Kplaque'_cc`
are now `IsComputablyCompactFamilyIn P B fun kr : ℕ × ℚ ↦ if 0 < kr.2 then G.Kplaque kr.2 (pIdx kr.1)
else ∅` (the `if` form was chosen: at `r ≤ 0` `Kplaque_spec` gives no compactness, and the empty
set is computably compact; the existence proof uses `Kplaque_spec … r hr` for `0 < r` and
`isCompact_empty` otherwise, with the oracle predicate stated for the `if` family).
Wave-2 additions (all proved): `isComputableRealFamilyIn_dist_of_names`, `IsREIn.exists_prefixList`,
`isCeOpenFamilyIn_dist_lt`, `IsCeOpenFamilyIn.compIn`, `IsCeOpenFamilyIn.biUnion_list`,
`PartrecIn.exists_list_mapM` (running a partial program along a list, via
`relative_closure_nat_rec`). Remaining sorries: `uPlus_represented`, `uMinus_represented` only.

Status (after the first follow-up): `lake env lean` reports exactly one error, the expected
`D_nonempty` field access in `exists_effectiveGeodesicData` (stale `GeometricData` olean; the
coordinator repaired that theorem and `IsCeOpenFamilyIn.inter`). Remaining `sorry`s:
`uPlus_represented`, `uMinus_represented` (true but heavy). `isAdmissible_f/finv`,
`birkhoff_uPlus/uMinus_computable` are proved modulo them.

Follow-up additions (all proved, in the `aux` section): `IsREIn.or`,
`IsREIn.exists_partrecIn_choice` (partial certified choice; `exists_computableIn_choice` is now
a corollary), `isREIn_mem_basicBall_of_names`, `isREIn_rat_lt_dist_names`,
`isREIn_rat_lt_dist_of_names` (strict lower bounds on the distance of two uniformly named
points), `exists_names_of_ballRel_uniform`, `IsRepresentedFamilyIn.names_uniform` (names of
`f i (x k)` uniformly in `(i, k)`; applied to `E.flow_represented` it gives the flow of a
computable family of points), `IsCeOpenFamilyIn.comp/union/iUnion/ite`,
`isCeOpenFamilyIn_lt_dist` (the sets `{w | ρ < dist w w₀}`),
`IsRepresentedFamilyIn.preimage_ceOpen`, `isREIn_fin_uniform` (finite disjunction over
`Fin n`), `IsComputablyCompactFamilyIn.subset_ceOpen_isREIn` (family version; the single
version is now a corollary).

## Unprovable / false as stated

### `IsCeOpenFamilyIn.inter`
- Statement: `IsCeOpenFamilyIn P A U → IsCeOpenFamilyIn P A V → IsCeOpenFamilyIn P A (fun i ↦ U i ∩ V i)`,
  with **no** hypothesis `ComputablePresentationIn P A`.
- Reason it is false in general: listing balls inside `U i ∩ V i` requires certifying
  `dist (ι k) (ι b.1) + t < b.2`, i.e. the metric table. Counterexample sketch: `X = ℝ`, `A = ∅`,
  a presentation with `ι 0 = 0`, `ι 1 = Ω` (Chaitin's number: left-c.e., not right-c.e.), all other
  ideal points rational; `U = ball (ι 0) 1`, `V = ball (ι 1) 1` (constant families, each c.e. with
  one listed ball). Then `U ∩ V = (Ω - 1, 1)`. A c.e. union of basic balls equal to it would have
  left endpoint `Ω - 1` as the infimum of a c.e. sequence of rationals `ι j - r` (centers `0`, `Ω`
  or rationals), making `Ω - 1`, hence `Ω`, right-c.e. Contradiction.
- Proposed fix: add `(hP : ComputablePresentationIn P A)`. The corrected statement is **proved**
  in the file as `IsCeOpenFamilyIn.inter_of_presentation` (rational distance certificates via
  `birkhoff_computableIn_lt` applied to the metric table; the listed balls `(k, t)` satisfy
  `dist (ι k) (ι b.1) < b.2 - t` and `dist (ι k) (ι b'.1) < b'.2 - t` for listed `b`, `b'`).

### `exists_effectiveGeodesicData`
- Statement: `∀ G P, ∃ B, Nonempty (EffectiveGeodesicData G P B)`.
- Reason it is unprovable: the field `secPt_mem : ∀ j k, secPt j k ∈ (G.box j).D` forces every
  section `(G.box j).D` to be nonempty, but no field of `GeodesicReconstructionData`/`FlowBox`
  guarantees this (a flow box with `U = D = ∅`, `τ = 0`, `a = 1`, together with `innerBox j = ∅`,
  satisfies every axiom as long as the other inner boxes still cover `X`).
- Proposed fix: add the hypothesis `∀ j, ((G.box j).D).Nonempty` (equivalently
  `((G.box j).U).Nonempty`, since `flow_τ_mem` sends `U` into `D`), or add such a field to
  `FlowBox`. The variant with this hypothesis is **proved** in the file as
  `exists_effectiveGeodesicData_of_nonempty`. Construction: `exists_admissible_base` for
  `(f, lamU, lamS)`; `exists_oracle_isREIn` for the sound ball relations of `φ q` (uniform in
  `q : ℚ`), of `τ_j`/`proj_j` on `U_j` (uniform in `j`), for `{(j, b) | ball b ⊆ innerBox j}` and for
  the three compactness-certificate predicates; `oracle_joins_tables` merges these seven oracles
  with an integer table coding the names of `pIdx` (row `pair 0 k`), the names of `secPt`
  (row `pair 1 (encode (j, k))`) and rational period approximations (row `pair 2 k`, decoded with
  `Computable.decode`). `pIdx (pair n m)` is a marked periodic point within `2⁻ᵐ` of `ι n`;
  `secPt j (pair n m)` is a section point within `2⁻ᵐ` of `ι n` when one exists.
  Chapter A's `FlowData.continuous_f` is used (still a `sorry` there).

## Left open (true, heavy)

### `uPlus_represented`, `uMinus_represented`
- `IsRepresentedMapIn P realPresentation B G.uPlus`, `uPlus x = (log 2)⁻¹ ∫₀¹ lamU (φ τ x) dτ`.
- Plausibly true (the relation only has to be `B`-c.e., so non-computable constants such as a
  rational `V' > G.V` may be hard-wired), but the proof is a substantial development:
  1. `IsComputablyCompactIn P B univ` from `innerBox_cc`, `innerBox_cover` (finite union over
     `Fin nBoxes`; `IsREIn` of `∀ j : Fin n, …` by `Finset.induction` with `IsREIn.and`);
  2. a semidecidable modulus certificate `Mod (ε, δ, t)`: "the first `t` listed pairs `(b, c)` of
     the relation of `lamU` with `c.2 < ε/2`, shrunk to radius `b.2 - δ`, cover `univ`" (prefix
     enumeration list as in `subset_ceOpen_isREIn`, semidecidable by 1, total by
     `lebesgue_number_lemma_of_metric`); it implies `dist x y < δ → |lamU x - lamU y| < ε`;
  3. Riemann sums: with `V'/N < δ`, `N⁻¹ ∑_{k<N} lamU (φ (k/N) x)` is within `ε` of the integral
     (`speed_unit`, `Flow.map_add`, `intervalIntegral.sum_integral_adjacent_intervals`,
     `intervalIntegral.norm_integral_le_of_norm_le_const`);
  4. shrink-closure `R⁺` of the relations of `lamU ∘ φ (k/N)` (listed `(b, c)` whenever some listed
     `(b', c)` has `dist (ι b.1) (ι b'.1) + b.2 < b'.2`, certified rationally), so that one input
     ball is listed with all `N` relations simultaneously (needed for completeness);
  5. rational approximations of `(log 2)⁻¹`: no computability result for `Real.log 2` exists in the
     library, so either prove `IsComputableRealFamilyIn ∅ (fun _ ↦ (Real.log 2)⁻¹)` (e.g. from the
     alternating series of `log 2`) or hard-wire a computable sequence of rational bounds;
  6. the relation `R_u (b, c) := 0 < b.2 ∧ 0 < c.2 ∧ ∃ ε δ t N cs l, Mod (ε, δ, t) ∧ V'/N < δ ∧
     (∀ k < N, R⁺_{k/N} (b, cs[k])) ∧ |l - (log 2)⁻¹| < η ∧ |c.center - l · N⁻¹ ∑ cs[k].center| +
     l · N⁻¹ ∑ cs[k].radius + l ε + η Λ' < c.2`, with the bounded quantifier over `cs` handled by a
     prefix-enumeration list and the sums by `Computable.nat_rec` with `Primrec.list_getD`.
- Estimated size: 400–600 lines. Not attempted.

## API facts useful for partial recursive searches in this project

- Oracle monotonicity: `RecursiveIn.subst hf (fun g hg ↦ by obtain rfl := Set.mem_singleton_iff.mp hg; exact hAB)`
  transports `PartrecIn/ComputableIn {charOracle A}` to `{charOracle B}` when
  `hAB : charOracle A ≤ᵀ charOracle B` (wrapped as `computableIn_mono_oracle`,
  `isComputableRealFamilyIn_mono_oracle`, `isRepresentedMapIn_mono_oracle` in the file;
  `IsREIn.mono_oracle` exists in `Oracle/Basic.lean`).
- Semidecidability of strict comparisons: `birkhoff_computableIn_lt A v hv :
  IsREIn A fun iq : α × ℚ ↦ v iq.1 < iq.2` (and `_gt`) for any `IsComputableRealFamilyIn A v`
  (`Dynamics/BowenBalls.lean`). Applied to the metric table (`hP : ComputablePresentationIn P A`
  is literally such a family indexed by `ℕ × ℕ`) this gives rational distance certificates; applied
  to `isComputableRealFamilyIn_dist_name` (new) it gives `isREIn_mem_basicBall`.
- `IsREIn` closure: `IsREIn.and`, `IsREIn.comp` (precompose with `ComputableIn` map),
  `IsREIn.exists` (project away the second factor), `isREIn_of_computable_decide`,
  `relative_enumeration` (c.e. ↔ computable `ℕ → Option α` enumeration).
- Effective choice (new, `IsREIn.exists_computableIn_choice`): from `IsREIn A G` on `α × β` and
  `∀ a, ∃ b, G (a, b)`, a `ComputableIn {charOracle A}` selector `g` with `∀ a, G (a, g a)`.
  Proof pattern for a dovetailed search: `Nat.rfindOpt (fun t ↦ (e t).bind fun w ↦ if encode w.1 =
  encode a then some w.2 else none)`, `PartrecIn.rfindOpt`, totality via `Nat.rfindOpt_dom`,
  then `PartrecIn.of_eq_tot` with `Part.get_mem`, and `Nat.rfindOpt_spec` for correctness.
  Compare encodings (`Primrec.eq` on `ℕ` with `Primrec.encode`) instead of using `DecidableEq α`.
- Uniform evaluation (new, `exists_names_of_ballRel`): an `IsREIn` family of ball pairs, sound and
  complete at a point with a computable name, yields names of all images uniformly in the index;
  the certificate predicate is `0 < c.2 ∧ c.2 < (2^p)⁻¹ ∧ ∃ b, R (i, b, c) ∧ x ∈ basicBall P b`.
- Prefix-enumeration lists: `fun it ↦ Nat.rec [] (fun s ih ↦ step (it.1, ih, e s)) it.2` is
  `ComputableIn` by `ComputableIn.nat_rec` with a plain `Computable step`
  (`Computable.option_casesOn`, `Primrec.ite`, `Primrec.list_cons`); membership
  `b ∈ L (i, t) ↔ ∃ s < t, e s = some (i, b)` by induction. This replaces bounded quantifiers
  `∀ b ∈ L, E (i, b)` (no `ComputableIn` list recursion exists) — see `subset_ceOpen_isREIn`.
- Elaboration pitfall: unifying a term against an expected type containing `Nat.pair` can time out
  (whnf of `Nat.pair`); build such `ComputableIn.comp` terms without an expected type (or with
  explicit `(f := …) (g := …)`) and `exact` afterwards (`computableIn_table_row`).
- Instance pitfall: `Computable.encode/decode` use `Primcodable.toEncodable`; for `ℚ` this is a
  different numbering from `Rat.instEncodable` (`Denumerable.ofEncodableOfInfinite`). Write
  `@Encodable.encode ℚ Primcodable.toEncodable` in tables that are decoded computably.
- Oracle construction: `exists_oracle_isREIn R` (any predicate is c.e. above some oracle),
  `exists_admissible_base`, `oracle_joins_tables C A v` (one oracle above `C`, above every `A j`,
  computing the integer table `v`), `Computable.decode` + `Option.getD` to read rationals back.
