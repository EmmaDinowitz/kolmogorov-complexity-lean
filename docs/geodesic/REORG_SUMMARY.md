# Overnight report — computability reorganization (2026-11-03)

Repository clone: `/home/user/alexeymilovanov/kolmogorov-complexity-lean` (nothing committed or pushed;
all changes on disk, `git status --short` lists 8 modified library files and 12 untracked paths).

## Result

* Steps 0–7 of `docs/geodesic/computability_reorg_blueprint.md` executed; log with per-step tables in
  `docs/geodesic/sorry_notes/REORG_LOG.md`, build logs `reorg_build*.log`, audit log `reorg_audit7.log`.
* `lake build KolmogorovMathlib` (whole library, 5476 jobs): exit 0, 0 errors, 0 warnings.
* `bash scripts/audit.sh`: AUDIT OK (strict sorry scan passed; nothing allowed by `AUDIT_ALLOW_SORRY`).
* **0 `sorry`** in the Geodesic chain (233 declarations). `main_pointwise`, `main_set` and
  `orbitToLocationEstimate_of_base` depend only on `propext`, `Classical.choice`, `Quot.sound`.
* Snapshots: `/home/user/backup_pre_reorg/` (state after wave 2) and `/home/user/backup_step{2..7}/`.

## Layout after the move

| layer | files | lines |
|---|---|---|
| 0 `Oracle/` | `Closure`, `Search`, `PrefixComplexity/NatBounds`, `PrefixComplexity/Decoders`, `Encoding/Numerals` | 1,079 |
| 1 `PointToSet/ComputableMetric/` | `Points`, `CeOpen`, `Compact`, `Represented` | 1,153 |
| 2 `PointToSet/EffectiveLocalization/` | `Search` (`certified_localization`, `_map`, `_point`), `Charging` (`precisionComplexity_le_of_program`) | 281 |
| 3 `PointToSet/Geodesic/` | `FlowInterface` (+`/OrbitExtension`), `GeometricData`, `EffectiveData`, `OrbitData`, `Localization`, `BracketApprox` (+`/Geometry`), `PlaqueNeighborhoods`, `SectionReconstruction`, `OrbitToLocation`, `UpperBound` (+`/Returns`, `/PrecisionChain`, `/SectionPoint`, `/Mixed`), aggregator `Geodesic.lean` | 9,464 |

All files are under 1,000 lines; every Geodesic module is listed in `KolmogorovMathlib.lean`;
Layer 1 imports only `Presentation.lean`, Layer 0 and Mathlib (the generic oracle lemmas it needed
moved from `Dynamics/BowenBalls` and `BirkhoffComputability` into `Oracle/Closure.lean`).
`docs/point_to_set_blueprint.md` gained a section "9. Effective localization layer" with the `eff:*`
and `geo:orbit-datum` node ids.

## Statement changes (everything else is verbatim moves and re-proofs)

1. **`OrbitDatum`** (`Geodesic/OrbitData.lean`): `idx`, `order`, `tol : ℝ`, `mem`. The Bowen-ball
   hypotheses of `bracket_approx(_forward/_backward)`, `net_approx`, `effective_neighborhoods`,
   `section_reconstruction` are now `∀ (dp : OrbitDatum P G.f x) (dm : OrbitDatum P G.finv x),
   dp.order = Tp + 1 → dp.tol ≤ … → dm.order = Tm + 1 → dm.tol ≤ … → … (dp.idx, dm.idx) …`.
   Program input types, `orbit_to_location` and all of Chapter I are unchanged.
2. **Quadrature sorries closed by assumption** (step 6). `EffectiveGeodesicData` has two new fields
   `admissible_f : IsAdmissible P G.f ![u⁺] B`, `admissible_finv : IsAdmissible P G.finv ![u⁻] B`
   (OTL §1 "effective quadrature of λ^{s/u}" is exactly the assumed step); `uPlus_represented`,
   `uMinus_represented` are projections. `exists_effectiveGeodesicData` still shows some oracle
   satisfies all fields, so the assumption is consistent. Deriving the fields from
   `lamU_represented`/`lamS_represented` alone remains an open optional lemma (plan in
   `docs/geodesic/sorry_notes/NOTES_C.md`, estimated 400–600 lines). **Please confirm you are happy with
   this as a hypothesis**; reverting is a one-field change plus the two sorries.
3. `IsCeOpenFamilyIn.inter_of_presentation` renamed to `IsCeOpenFamilyIn.inter` (the `hP` version;
   the counterexample for the `hP`-free statement was not formalized).
4. Deleted (no call sites): `proj_mem_plaques`, `flow_coordinate_proj`, the pre-`OrbitDatum` forms
   of `orbit_approximants`, `abs_birkhoff_*`, `exists_computable_scale*`.
5. Library: eleven formerly `private` lemmas in `Dynamics/BirkhoffComputability.lean` and
   `ComputableMetric/Presentation.lean` are public; six helpers in the former `UpperBound.lean` lost
   `private` because the split put their uses in other files.

## Debt left (recorded in the log)

* `mixed_core` (`UpperBound/Mixed.lean`, 640-line proof) needs `maxHeartbeats 1600000`; the file
  is in `scripts/resource_override_allowlist.txt`. Fix: split the proof into named lemmas.
* One `cut_quality` allow-list row (`section_localization`, SINGLE-USE-TAIL).
* Deferred by design: the `LocalizationCode` record for program inputs (would force re-deriving
  every `PartrecIn` projection proof), `OrbitDatum` as a program input, the list-input
  generalization of `precisionComplexity_le_of_program` (no use site).

## Other deliverables from tonight

* `/home/user/geometric_dependencies.pdf` — the list of geometric assumptions (FlowData, FlowBox,
  G1–G12 with sources and consumers, Chapter B derived lemmas) you asked for.
* `/home/user/geodesic_upper_bound_blueprint_v2.md` Section 9 regenerated with the final inventory.
