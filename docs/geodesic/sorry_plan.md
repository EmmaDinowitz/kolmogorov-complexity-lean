# Plan: filling the 185 sorries of `KolmogorovMathlib/PointToSet/Geodesic/`

Repository clone: `/home/user/alexeymilovanov/kolmogorov-complexity-lean` (Lean 4.35.0, Mathlib cache present).
Check one file without touching the build tree: `lake env lean <file>` (about 20 s).
Full serialized rebuild at the end: `lake build KolmogorovMathlib.PointToSet.Geodesic.UpperBound`.

## Rules for the whole run

1. Proofs only. No statement, definition or field is changed silently. If a statement is false or
   unprovable from the available hypotheses, the `sorry` stays and the reason goes to
   `docs/geodesic/sorry_notes/NOTES_<module>.md` with a proposed fix (new field, changed hypothesis).
2. One worker per file. Workers check with `lake env lean` only; `lake build` is run once, serially,
   at the end. Downstream modules keep their old `.olean`s, which stay valid because statements do
   not change.
3. Every filled proof must leave the file compiling with no errors (warnings for remaining
   `sorry`s are expected). Keep the 100-character line limit and the repository's docstring style.

## Classification of the 185 sorries

| module | sorries | kind | expected outcome overnight |
|---|---|---|---|
| FlowInterface (A) | 42 | real analysis, `liminf`/`limsup`, library wrappers; 2 programs (`orbit_extension`, normalized form) | all but possibly the two programs |
| GeometricData (B) | 28 | consequences of fields G1–G12 | most; `flow_shift_eq_of_mem_plaque_u` is not derivable from the fields and should become a field; `plaque_expansivity` depends on it |
| EffectiveData (C) | 35 | relative computability wrappers; one existence theorem | wrappers; `exists_effectiveGeodesicData` likely stays |
| Localization (D) | 12 | 2 topology lemmas, uniqueness, 4 programs | topology, uniqueness, `shadowSet_compl_ceOpen`; programs likely partial |
| BracketApprox (E) | 14 | 6 scale lemmas, 2 geometric steps, 3 programs, 2 covering | scale lemmas, covering; geometric steps attempted; programs likely stay |
| PlaqueNeighborhoods (F) | 12 | 5 pure covering lemmas, 4 quadrature/scale, 1 program, 2 misc | all but the program |
| SectionReconstruction (G) | 9 | 3 consequences of G11, code lemma, localization, 1 program, 1 identity | all but the program |
| OrbitToLocation (H) | 14 | 4 scale identities, 6 bookkeeping, 4 main/specialization | identities and bookkeeping; main theorems depend on G's program |
| UpperBound (I) | 19 | definitions' lemmas, stopping times, return adjustment, chain, two section-point bounds, flow coordinate, main theorems | pure limit lemmas and bookkeeping; `sectionPoint_upper` attempted; `main_set` from the library theorems |

## Waves

* **Wave 1 (parallel, now):** A, B, C wrappers, F+G+H pure parts, I pure parts. Independent files,
  no cross-file statement changes.
* **Wave 2:** D programs (need C's wrappers), E programs (need D), F/G/H programs (need E), I main
  bounds (need A's denominator swap and H's statements). Sequential by dependency; parallel where files differ.
* **Wave 3:** serial `lake build`, reconcile notes, update `geodesic_upper_bound_blueprint.md`
  Section 14 with what was proved and what remains, with reasons.

## Known design items to resolve before certain sorries can close

* Shrinkable plaque family (Chapters B–C) before `orbitToLocationEstimate_of_smallPlaques` can lose
  its hypothesis. Not attempted tonight; recorded.
* Backward (stable) expansivity for `localization_decoder_backward`.
* `flow_shift_eq_of_mem_plaque_u` (transversality of unstable plaques to the flow) as a field.
