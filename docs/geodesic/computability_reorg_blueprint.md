# Blueprint: reorganizing the computability-theoretic content

Scope: the effectiveness layer of `KolmogorovMathlib/PointToSet/Geodesic/*.lean` (about 60 % of its
10,600 lines), reorganized into four layers so that everything independent of the geodesic
geometry lives in the library and the geometric chapters shrink to estimates plus instantiations.
This is a refactor of proved material: no mathematics changes, no `sorry` is introduced, and the
build must stay green after every step (Section 6).

Prerequisite: wait for the current second wave to finish (BracketApprox `net_approx`, UpperBound
`flow_coordinate`), run the serial `lake build`, and start from that state.

---

## 0. Target layering

```
Layer 0  Oracle/                      relative computability toolkit, no metric space
Layer 1  ComputableMetric/            effective topology of a Presentation, no dynamics
Layer 2  PointToSet/EffectiveLocalization/   certified search + decoder charging, no dynamics
Layer 3  PointToSet/Geodesic/         orbit data, periodic enumeration, flow boxes, programs
```

Each layer imports only lower layers. The geometric structure `GeodesicReconstructionData` and
all of Chapter B stay as they are (they contain no effectiveness).

---

## 1. Layer 0 — `Oracle/` additions

New file `Oracle/Closure.lean` (or append to `Oracle/Basic.lean`), namespace `Kolmogorov.PointToSet`.

| declaration (current location) | target | note |
|---|---|---|
| `computableIn_mono_oracle`, `isComputableRealFamilyIn_mono_oracle`, `isRepresentedMapIn_mono_oracle` (EffectiveData) | `Oracle/Closure.lean` | one lemma `PartrecIn.mono_oracle` plus three corollaries; `IsREIn.mono_oracle` already exists in `Oracle/Basic.lean` |
| `IsREIn.or`, `IsREIn.and`, `IsREIn.exists`, `IsREIn.comp`, `isREIn_fin_uniform`, `IsREIn.list_forall_get` (EffectiveData, FlowInterface) | `Oracle/Closure.lean` | closure of c.e. predicates: disjunction (interleave), conjunction, projection, reindexing along a computable map, `Fin n`-uniformization, position-indexed bounded `∀` over a `List` |
| `IsREIn.exists_partrecIn_choice`, `IsREIn.exists_computableIn_choice` (EffectiveData) | `Oracle/Search.lean` | the dovetailed first-certified-candidate search, partial and total forms. This is the single lemma every decoder is built on |
| `oracleNatComplexity_le_log_add_loglog` (FlowInterface) with its private `tsum_inv_two_pow_size_mul_le` | `Oracle/PrefixComplexity/NatBounds.lean` | `K^A(n) ≤ log₂(n+1) + 2 log₂(log₂(n+1)+1) + c` via `oracle_kraftChaitin_bound` |
| `oracleNatComplexity_le_of_decoder`, `partrecIn_mono`, `oraclePairComplexity_le_log`, `oraclePairComplexity_sublinear` (OrbitToLocation) | `Oracle/PrefixComplexity/Decoders.lean` | decoder charging: composition of `k` fixed-arity natural inputs through `natBits` / `pairCode`; generalize to `k` inputs as a `List ℕ` version `oracleNatComplexity_le_of_decoder_list` |
| the private digit/numeral helpers of `orbit_extension` (`digitAt`, `natPowRec`, `ofDigits_append_one_*`) (FlowInterface) | `Oracle/Encoding/Numerals.lean` | base-`N` itinerary numerals with a leading `1`; reusable for any itinerary coding |

Make public (library change, no proof change): the private lemmas in
`PointToSet/Dynamics/BirkhoffComputability.lean` lines 46–266 (`exists_constant_oracle_indices`,
`exists_oracle_specialization`, `exists_iterate_indices`, `isCauchyName_of_iterate_indices`,
`computable_names_of_total_oracle_indices`, `exists_computable_orbit_names`,
`computable_orbit_distances`) and in `ComputableMetric/Presentation.lean`
(`mem_basicBall_iff_exists_certificate`, `computable_inv_two_pow`, `exists_basicBall_radius_lt`,
`cast_inv_two_pow`). Then delete the verbatim copies in FlowInterface (`section orbitNames`) and
EffectiveData (`isComputableRealFamilyIn_dist_names_local`).

---

## 2. Layer 1 — `ComputableMetric/` additions

New files under `PointToSet/ComputableMetric/`: `Points.lean`, `CeOpen.lean`, `Compact.lean`,
`Represented.lean`.

| declaration (current location) | target | note |
|---|---|---|
| `IsComputablePointIn`, `isComputablePointIn_ι`, `IsComputablePointIn.map`, `isComputablePointIn_mono`, `exists_isCauchyName`, `isCauchyName_const` | `Points.lean` | computable points of a presentation |
| `isComputableRealFamilyIn_dist_names`, `_dist_name`, `isREIn_mem_basicBall_of_name(s)`, `isREIn_rat_lt_dist_names`, `isREIn_rat_lt_dist_of_names`, `exists_mem_basicBall_radius_lt` | `Points.lean` | strict distance certificates from names: the "dovetailed strict inequality" idiom, proved once |
| `IsCeOpenIn`, `IsCeOpenFamilyIn`, `.union`, `.inter_of_presentation` (rename to `.inter`, with `hP`), `.iUnion`, `.ite`, `.comp`, `isCeOpenFamilyIn_ball`, `isCeOpenFamilyIn_lt_dist`, `isOpen_eq_biUnion_basicBall`, `isCeOpenFamilyIn_mono`, `ballUnion`, `ballUnion_ceOpen` (PlaqueNeighborhoods) | `CeOpen.lean` | c.e. open sets and families; the counterexample showing `hP` is needed for `inter` goes to `KolmogorovCounterexamples` |
| `IsComputablyCompactIn`, `IsComputablyCompactFamilyIn`, `.subset_ceOpen_isREIn` (both), `isComputablyCompactFamilyIn_mono` | `Compact.lean` | effective compactness as semidecidable containment in finite unions of basic balls |
| `IsRepresentedOnIn`, `IsRepresentedMapIn.onSubset`, `IsRepresentedOnIn.map`, `isRepresentedOnIn_mono` | `Represented.lean` | representation on a subset (for maps continuous only on an open set) |
| `IsRepresentedFamilyIn`, `.apply`, `.names`, `.names_uniform`, `.preimage_ceOpen`, `exists_names_of_ballRel(_uniform)`, `isRepresentedFamilyIn_mono`, `exists_basicBall_image_subset_of_continuousAt` | `Represented.lean` | uniform families indexed by a primcodable type; pullback of c.e. open families |
| `exists_basicBall_code` (SectionReconstruction) | `CeOpen.lean` | an open set containing `z` contains a coded basic ball `basicBall P (c, rV)` around `z` |

Interface change recorded here (S4 of the v2 blueprint): `IsAdmissible` stays the library's
notion; the Geodesic structure stops restating items the library already has (Section 4).

---

## 3. Layer 2 — `PointToSet/EffectiveLocalization/` (new)

Two files, no dynamics.

**`Search.lean`.** The theorem all decoders instantiate (currently the private
`decoder_of_compl_ceOpen` in Localization.lean):

```
theorem certified_localization {κ : Type*} [Primcodable κ] (P : Presentation X) (A : Set ℕ)
    {K : κ → Set X} (hK : IsComputablyCompactFamilyIn P A K)
    {O : κ → Set X} (hO : IsCeOpenFamilyIn P A O) (hP : ComputablePresentationIn P A) :
    ∃ loc : κ × ℕ →. ℕ, PartrecIn {charOracle A} loc ∧
      ∀ k p, ∀ S : Set X, S ⊆ K k → K k \ S = K k ∩ O k → S.Nonempty → S.Subsingleton →
        (loc (k, p)).Dom ∧ ∀ q ∈ loc (k, p), ∀ z ∈ S, dist (P.ι q) z < dyadicRadius p
```
plus `certified_localization_map`: the same with the output within `2⁻ᵖ` of `f z` for a map `f`
represented on `K k` (the `_proj` variant), and `certified_localization_point`: the computable-point
corollary. Proof: the existing one (certificate "`K k ⊆ O k ∪ ball(c, 2⁻ᵖ)`", `exists_partrecIn_choice`).

**`Charging.lean`.** The complexity account of a program applied to shortest descriptions:

```
theorem precisionComplexity_le_of_program (P : Presentation X) (A : Set ℕ)
    (F : ℕ × ℕ × ℕ × ℕ →. ℕ) (hF : PartrecIn {charOracle A} F) :
    ∃ c : ℕ, ∀ (z : X) (δ : ℝ) (i i' Tp Tm : ℕ), (∀ q ∈ F (i, i', Tp, Tm), dist (P.ι q) z < δ) →
      (F (i, i', Tp, Tm)).Dom →
      precisionComplexityNat P A z δ ≤
        oracleNatComplexity A i + oracleNatComplexity A i' + oraclePairComplexity A Tp Tm + c
```
with the list-input generalization. Chapter H's `orbit_to_location` becomes: `section_reconstruction`
gives the program and its error bound; this lemma gives the inequality.

---

## 4. Layer 3 — the Geodesic chapters after the move

**`Geodesic/OrbitData.lean` (new).** One abstraction replacing the bare tuples:

```
structure OrbitDatum (P : Presentation X) (T : X → X) (x : X) where
  idx : ℕ          -- ideal index
  order : ℕ        -- number of observed times, `T + 1` for the orbit on `[0, T]`
  tol : ℚ          -- rational tolerance
  mem : P.ι idx ∈ bowenBall T order x tol
```
with the two derived facts, currently `orbit_approximants` (names of `φ q (ι idx)` at rational
times, within `L · tol` of `φ q x` on the window) and the quadrature bound currently
`abs_birkhoff_uPlus_sub_le`, and the computable scales `exists_computable_scalePlus/Minus`.
`orbitComplexityNat` is the minimum of `oracleNatComplexity A d.idx` over data of given order and
tolerance; record this as `orbitComplexityNat_eq_iInf_orbitDatum`.

**`Geodesic/EffectiveData.lean` (slimmed).** `EffectiveGeodesicData` keeps only what the library
has no notion for: `IsAdmissible P f ![u⁺] B`, `IsAdmissible P finv ![u⁻] B`, the flow at rational
times (`IsRepresentedFamilyIn P P B fun q : ℚ ↦ φ q`), the periodic enumeration with names,
periods and radius-indexed computably compact plaques, and the flow-box atlas (`τ`, `proj`
represented on the domains, inner boxes c.e. open with computably compact closures, dense
computable section sequences, nonempty sections). `mono` and `exists_effectiveGeodesicData` stay.
Everything in its current `aux` and `notions` sections moves to Layers 0–1.

**Programs stated as program + account.** Each of `localization_decoder(_proj/_backward)`,
`bracket_approx_forward/backward`, `net_approx`, `effective_neighborhoods`, `section_reconstruction`
is split into (a) a named program definition `def … : <input type> →. <output>` with its
`PartrecIn` proof, (b) a correctness theorem on valid inputs, (c) where relevant a complexity
account using `Charging.lean`. Input types are built from `OrbitDatum` and a `LocalizationCode`
record `(j : Fin nBoxes) (s : ℚ) (c : ℕ) (rV r : ℚ)` instead of nested products.

**Deletions.** The `section orbitNames` copies in FlowInterface; `isComputableRealFamilyIn_dist_names_local`;
the three in-file re-derivations of "finite conjunction of strict distance certificates is c.e."
(replaced by `Points.lean`); `proj_mem_plaques` (superseded by `dW_cs_flow_self` used directly);
`flow_coordinate_proj` (corollary no longer on the main path).

---

## 5. Current → target map of the main program chain

| current (file) | target | depends on |
|---|---|---|
| `decoder_of_compl_ceOpen` (Localization, private) | `EffectiveLocalization.certified_localization` | Layers 0–1 |
| `localization_decoder`, `_proj`, `_backward`, `localization_core` | instances in `Geodesic/Localization.lean` | `certified_localization(_map)`, `shadowSet_compl_ceOpen` |
| `shadowSet_compl_ceOpen` | `Geodesic/Localization.lean` | `Represented.preimage_ceOpen`, `CeOpen.iUnion/union/ite`, `OrbitDatum` names |
| `bracket_approx_*` | `Geodesic/BracketApprox.lean`, program + correctness | decoders, `bracket_construction_mem_shadowSet`, `_error` |
| `net_approx` | same | `Compact.subset_ceOpen_isREIn`, bracket programs |
| `effective_neighborhoods` | `Geodesic/PlaqueNeighborhoods.lean` | `net_approx`, computable scales |
| `section_reconstruction` | `Geodesic/SectionReconstruction.lean` | `effective_neighborhoods`, `exists_basicBall_code`, `Search` idiom on shifted section points |
| `orbit_to_location` | `Geodesic/OrbitToLocation.lean` | `section_reconstruction`, `Charging.precisionComplexity_le_of_program` |
| `OrbitToLocationEstimate`, `main_pointwise`, `main_set` | `Geodesic/UpperBound.lean` | unchanged |

---

## 6. Migration order (build stays green at each step)

1. **Publish library privates** (Section 1, last paragraph): remove `private` on the listed lemmas
   in `Dynamics/BirkhoffComputability.lean` and `ComputableMetric/Presentation.lean`. Build.
2. **Create Layer 0 files** by moving declarations verbatim from EffectiveData / FlowInterface /
   OrbitToLocation; leave `export`-style aliases (`alias foo := Kolmogorov.PointToSet.foo`) in the
   old files for one step. Build.
3. **Create Layer 1 files** the same way; `IsCeOpenFamilyIn.inter` becomes the `hP` version only.
   Build.
4. **Create Layer 2**: generalize `decoder_of_compl_ceOpen` to `certified_localization` (index
   type `κ`), add `certified_localization_map` and `Charging.lean`. Re-prove the four Chapter D
   decoders as instances. Build.
5. **Introduce `OrbitDatum`** and restate `orbit_approximants`, the quadrature bounds and the
   computable scales through it; restate decoder inputs. This is the only step that changes
   statement shapes; do it chapter by chapter D → E → F → G → H, rebuilding after each.
6. **Slim `EffectiveGeodesicData`** to Section 4; replace uses of the removed fields by the
   library predicates. Build.
7. **Delete** the copies and superseded lemmas; remove the aliases of step 2. Build; run
   `scripts/audit.sh` with `AUDIT_ALLOW_SORRY=1` (two optional sorries may remain in quadrature) and
   fix docstring coverage and import hygiene; regenerate `docs/point_to_set_blueprint.md` entries
   with the new node ids `eff:*`.

Expected sizes after the move: Layers 0–2 about 3,500 lines (reusable), Geodesic chapters about
4,500 lines (geometry 1,800, programs and instantiations 1,700, Chapter I 1,000 after removing
duplicated limit helpers).

---

## 7. Node ids for the point-to-set blueprint document

Layer 0: `eff:closure`, `eff:search`, `eff:nat-bounds`, `eff:decoder-charging`, `eff:numerals`.
Layer 1: `eff:points`, `eff:distance-certificates`, `eff:ce-open`, `eff:compact`,
`eff:represented-on`, `eff:represented-family`.
Layer 2: `eff:certified-localization`, `eff:certified-localization-map`, `eff:program-account`.
Layer 3 keeps the `geo:*` ids of blueprint v2, with `geo:orbit-datum` added.

---

## 8. Acceptance criteria

* Every Geodesic module imports Layers 0–2 and `Geodesic/GeometricData.lean` only through the
  intended dependency order; `import_hygiene.py --check` passes.
* No declaration in `Geodesic/` mentions `PartrecIn` except the program definitions of Section 4.
* No duplicated statement between `Geodesic/` and the library (checked by `check_dup_decls.py`).
* `lake build KolmogorovMathlib` succeeds; the `sorry` scan reports at most the two quadrature
  lemmas; docstring coverage 100 % on the new files.
