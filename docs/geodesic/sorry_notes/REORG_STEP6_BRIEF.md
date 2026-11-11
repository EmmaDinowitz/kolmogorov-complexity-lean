# Brief for reorganization step 6 — slim `EffectiveGeodesicData`

Repository: /home/user/alexeymilovanov/kolmogorov-complexity-lean (`export PATH="$HOME/.elan/bin:$PATH"`).
Blueprint: docs/geodesic/computability_reorg_blueprint.md Section 4 ("EffectiveData.lean (slimmed)")
and step 6 of Section 6. Log: docs/geodesic/sorry_notes/REORG_LOG.md (steps 0–5 done).
Backup before starting: copy `KolmogorovMathlib/PointToSet/Geodesic` to /home/user/backup_step6/.

## Current structure (KolmogorovMathlib/PointToSet/Geodesic/EffectiveData.lean)

Fields: `presentation`, `flow_represented`, `lamU_represented`, `lamS_represented`, periodic
enumeration (`pIdx`, `pIdx_mem`, `pIdx_dense`, `pIdx_names`, `period*`, `Kplaque_cc`,
`Kplaque'_cc`), flow-box atlas (`box_τ`, `box_proj`, `innerBox_ceOpen`, `innerBox_cc`, `secPt*`).
All its former `aux`/`notions` sections already moved to Layers 0–1 in steps 2–3, so the structure
is already close to the target. Remaining changes:

1. **Unit potentials as admissibility.** Replace the two fields `lamU_represented`,
   `lamS_represented` by
   ```
   /-- (3) The base oracle is admissible for the time-one map with the forward unit potential. -/
   admissible_f : IsAdmissible P G.f (fun _ : Fin 1 ↦ G.uPlus) B
   /-- (3) … and for its inverse with the backward unit potential. -/
   admissible_finv : IsAdmissible P G.finv (fun _ : Fin 1 ↦ G.uMinus) B
   ```
   and *keep* `lamU_represented`, `lamS_represented` as fields too (they are the drafts' hypothesis
   and are used by nothing downstream except the quadrature derivation; keeping them preserves the
   interface). Then `uPlus_represented`, `uMinus_represented`, `isAdmissible_f`,
   `isAdmissible_finv`, `isAdmissible_rates` become projections, and the two `sorry`s disappear.
   Record prominently in the log: the two quadrature sorries are closed by **assuming** the unit
   potentials represented (OTL §1 "effective quadrature of λ^{s/u}" is exactly this derivation);
   the derivation from `lamU_represented` alone remains an open, optional lemma (plan in
   docs/geodesic/sorry_notes/NOTES_C.md). `presentation` and `f_represented` may then be derived from
   `admissible_f.1/.2.1`; keep `presentation` as a field if removing it touches many call sites
   (`E.presentation` is used widely) — prefer keeping it.
2. **Existence.** Extend `exists_effectiveGeodesicData_of_nonempty` / `exists_effectiveGeodesicData`
   to produce the new fields: the proof builds an oracle from tables (`computableIn_table_row`);
   add table rows for `G.uPlus`/`G.uMinus` at ideal points (they are continuous on a compact space,
   `uPlus_props`, so rational approximations exist exactly like for `lamU`). Follow the pattern used
   for `lamU_represented` in that proof.
3. **`mono`.** Extend `EffectiveGeodesicData.mono` with the new fields (`IsAdmissible` is monotone
   in the oracle: `ComputablePresentationIn`, `IsRepresentedMapIn` monotonicity lemmas exist:
   `isRepresentedMapIn_mono_oracle` in ComputableMetric/Represented.lean, `computableIn_mono_oracle`
   in Oracle/Closure.lean, and whatever `mono` already uses for `presentation`).
4. Nothing else in the structure changes. Statements of all downstream theorems unchanged.

## Gates and logging

`lake build KolmogorovMathlib.PointToSet.Geodesic.UpperBound > docs/geodesic/sorry_notes/reorg_build6.log 2>&1`
exit 0, **zero `sorry` warnings** after this step. Docstrings, line length, scripts as in the other
briefs. Log: table row for step 6 and a "Step 6 notes" section with the final field list of
`EffectiveGeodesicData`, the statement that the quadrature sorries were closed by assumption, and
line counts. Never commit or push.
