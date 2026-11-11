# Brief for reorganization step 7 — deletions, hygiene, audit

Repository: /home/user/alexeymilovanov/kolmogorov-complexity-lean (`export PATH="$HOME/.elan/bin:$PATH"`).
Blueprint: docs/geodesic/computability_reorg_blueprint.md Section 4 ("Deletions"), step 7 of
Section 6, Section 7 (node ids), Section 8 (acceptance). Log: docs/geodesic/sorry_notes/REORG_LOG.md.
Backup before starting: copy `KolmogorovMathlib/PointToSet/Geodesic`, `KolmogorovMathlib/Oracle`,
`KolmogorovMathlib/PointToSet/ComputableMetric`, `KolmogorovMathlib/PointToSet/EffectiveLocalization`,
`KolmogorovMathlib/PointToSet/Dynamics` and `KolmogorovMathlib.lean` to /home/user/backup_step7/.

## 7a. Deletions and superseded names
* `IsCeOpenFamilyIn.inter_of_presentation` → keep only `IsCeOpenFamilyIn.inter` (rename call sites).
* `proj_mem_plaques` (GeometricData or PlaqueNeighborhoods; superseded by `dW_cs_flow_self` used
  directly) — delete only if it has no call sites; otherwise leave and log.
* `flow_coordinate_proj` (UpperBound.lean) — delete only if unused on the main path
  (`main_pointwise`, `main_set`); otherwise leave and log.
* `orbit_approximants(_backward)` corollaries, `abs_birkhoff_*`, `exists_computable_scale*` old
  forms: delete if every call site uses the `OrbitDatum` form; otherwise keep.
* Any `alias`/one-line wrappers introduced in steps 2–5 that have no remaining call site.
Build gate after 7a.

## 7b. Layering fix (deferred from step 3)
`ComputableMetric/Points.lean` imports `PointToSet/Dynamics/BowenBalls` for the generic oracle
lemmas `birkhoff_computableIn_lt/gt`, `computable_rat_inv_two_pow`, `exists_two_mul_inv_two_pow_lt`
(+ BowenBalls' private helpers they need) and `IsComputableRealFamilyIn.comp`
(BirkhoffComputability). Move those lemmas verbatim to `Oracle/Closure.lean` (or `Oracle/Basic.lean`
if they only need its imports), make BowenBalls/BirkhoffComputability import them from there, and
drop the Dynamics import from Points.lean. Acceptance: Layer 1 files import only Presentation.lean,
Layer 0 and Mathlib. Build gate: `lake build KolmogorovMathlib` (the whole library, since
BowenBalls/BirkhoffComputability are widely imported).

## 7c. Module list, sizes, warnings
* Add the ten Geodesic modules (`FlowInterface`, `GeometricData`, `EffectiveData`, `OrbitData`,
  `Localization`, `BracketApprox`, `PlaqueNeighborhoods`, `SectionReconstruction`,
  `OrbitToLocation`, `UpperBound`) to `KolmogorovMathlib.lean` alphabetically; create the
  aggregator `KolmogorovMathlib/PointToSet/Geodesic.lean` in the style of
  `KolmogorovMathlib/PointToSet/ComputableMetric.lean` and list it too.
* File-size gate (`scripts/audit.sh`, 1,000 lines): for every Geodesic file over 1,000 lines
  either split at a natural topical boundary (UpperBound.lean at ~2,400 lines should become e.g.
  `UpperBound/Returns.lean` (ControlledReturns, PositiveRates, stopping times, return adjustment),
  `UpperBound/SectionPoint.lean` (precision chain, sectionPoint bounds, flow coordinate),
  `UpperBound.lean` (interface, main theorems) — check the dependency order first) or add a row to
  `docs/history/size_allow.tsv` with a specific reason (see the file's existing rows and
  `scripts/size_allow.py --check` for the required form). Prefer splitting UpperBound and
  BracketApprox; use allow-list rows for files between 1,000 and 1,300 lines when no natural
  boundary exists.
* Fix the cosmetic linter warnings in the Geodesic files (`show` → `change`, deprecated
  `if_pos/if_neg` → `ite_eq_left_of_eq_true`/`ite_eq_right_of_eq_false` or `if_pos`'s suggested
  replacement, unused binders → `_`-prefixed). Zero warnings on the chain build is the target.

## 7d. Audit and docs
* `AUDIT_ALLOW_SORRY=1 bash scripts/audit.sh` (after step 6 there should be no sorry at all; if the
  audit still complains about something unrelated to this work, record it and do not touch other
  parts of the repository). Also `python3 -B scripts/docstring_coverage.py --check`,
  `python3 -B scripts/check_headers.py --by-name`, `python3 -B scripts/import_hygiene.py --check`,
  `python3 -B scripts/check_dup_decls.py | tail -1` (baseline 34). If the audit regenerates
  `docs/SUV_COVERAGE.md`, let it.
* `docs/point_to_set_blueprint.md`: add entries, in the file's existing bullet format
  (`* **\`id\`** — one-sentence statement. \`Fully.Qualified.Name\` (\`path\`); same file: …`),
  for the Layer 0–2 node ids of blueprint Section 7: `eff:closure`, `eff:search`,
  `eff:nat-bounds`, `eff:decoder-charging`, `eff:numerals`, `eff:points`,
  `eff:distance-certificates`, `eff:ce-open`, `eff:compact`, `eff:represented-on`,
  `eff:represented-family`, `eff:certified-localization`, `eff:certified-localization-map`,
  `eff:program-account`, and `geo:orbit-datum`. Put them in a new section
  "Effective localization layer" placed before the geodesic material (or at the end if there is no
  geodesic section yet).
* Final full build: `lake build KolmogorovMathlib > docs/geodesic/sorry_notes/reorg_build7_full.log 2>&1`.

## Logging
Table row for step 7 and a "Step 7 notes" section: deletions, moved lemmas (7b), file splits with
the new module names, allow-list rows added, audit output summary, final line counts of every
Geodesic/Oracle/ComputableMetric/EffectiveLocalization file, final sorry count (expected 0).
Never commit or push.
