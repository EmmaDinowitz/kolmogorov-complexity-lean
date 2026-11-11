# Brief for reorganization step 4 — Layer 2 `PointToSet/EffectiveLocalization/`

Repository: /home/user/alexeymilovanov/kolmogorov-complexity-lean (`export PATH="$HOME/.elan/bin:$PATH"`).
Blueprint: docs/geodesic/computability_reorg_blueprint.md Section 3 and step 4 of Section 6.
Log: docs/geodesic/sorry_notes/REORG_LOG.md (steps 0–3 done when this step starts).
Backup before starting: copy `KolmogorovMathlib/PointToSet/Geodesic` to /home/user/backup_step4/.

## Search.lean (`KolmogorovMathlib/PointToSet/EffectiveLocalization/Search.lean`)

Generalize the private `decoder_of_compl_ceOpen` of `Geodesic/Localization.lean` (section
`decoder`) to a single index type:

```
theorem certified_localization {κ : Type*} [Primcodable κ] {P : Presentation X} {A : Set ℕ}
    {K : κ → Set X} (hK : IsComputablyCompactFamilyIn P A K)
    {O : κ → Set X} (hO : IsCeOpenFamilyIn P A O) (hP : ComputablePresentationIn P A) :
    ∃ loc : κ × ℕ →. ℕ, PartrecIn {charOracle A} loc ∧
      ∀ k p, ∀ S : Set X, S ⊆ K k → K k \ S = K k ∩ O k → S.Subsingleton →
        ∀ z₀ ∈ S, (loc (k, p)).Dom ∧ ∀ q ∈ loc (k, p), dist (P.ι q) z₀ < dyadicRadius p
```
The proof is the existing one (certificate `K k ⊆ O k ∪ ball (ι c) 2⁻ᵖ`, `exists_partrecIn_choice`),
with the five-fold projections replaced by `Prod.fst`/`Prod.snd` on `κ × ℕ`. Then:

* `certified_localization_map`: same hypotheses plus a map `f : X → Y` with a c.e. relation
  `R` representing `f` on each `K k` (the shape used in `localization_decoder_proj`: `hbox`),
  output within `dyadicRadius p` of `f z₀`. Extract the proof from `localization_decoder_proj`
  (the `Ecert` certificate: a listed output ball certified inside `ball (ι c) 2⁻ᵖ`).
* `certified_localization_point`: if `S = {z₀}` for all `p`, then `IsComputablePointIn P A z₀`
  (the body of `isComputablePointIn_of_shadowSet`).

Re-prove in `Geodesic/Localization.lean` as instances: `localization_decoder`
(`κ := ℕ × ℚ × ℕ × ℕ × ℕ`, `K (kp, r, _, _, _) := if 0 < r then G.Kplaque r (E.pIdx kp) else ∅`
reindexed through `Kplaque_cc`), `localization_decoder_proj`, `localization_decoder_backward`,
`isComputablePointIn_of_shadowSet`. Their statements do not change. Delete
`decoder_of_compl_ceOpen`.

## Charging.lean (`KolmogorovMathlib/PointToSet/EffectiveLocalization/Charging.lean`)

Move from `Geodesic/OrbitToLocation.lean`: `precisionComplexityNat_anti`,
`precisionComplexityNat_le_of_dist_lt`, and state

```
theorem precisionComplexity_le_of_program (P : Presentation X) (A : Set ℕ)
    (F : ℕ × ℕ × ℕ × ℕ →. ℕ) (hF : PartrecIn {charOracle A} F) :
    ∃ c : ℕ, ∀ (z : X) (δ : ℝ) (i i' Tp Tm : ℕ), (F (i, i', Tp, Tm)).Dom →
      (∀ q ∈ F (i, i', Tp, Tm), dist (P.ι q) z < δ) →
      precisionComplexityNat P A z δ ≤
        oracleNatComplexity A i + oracleNatComplexity A i' + oraclePairComplexity A Tp Tm + c
```
proved from `oracleNatComplexity_le_of_decoder` (now in `Oracle/PrefixComplexity/Decoders.lean`)
and `precisionComplexityNat_le_of_dist_lt`. Rewrite the complexity step of `orbit_to_location`
to use it (statement unchanged). If `orbit_to_location` charges a program with a different input
arity, add the matching `_list` or arity variant instead of changing the geodesic statement.

## Gates and logging

Build gate: `lake build KolmogorovMathlib.PointToSet.Geodesic.UpperBound` exit 0, no errors.
Add the two new modules to `KolmogorovMathlib.lean`. Docstrings on every declaration, lines ≤ 100,
new files < 1,000 lines, `python3 -B scripts/docstring_coverage.py --check`,
`python3 -B scripts/check_headers.py`, `python3 -B scripts/import_hygiene.py --check`.
Log: table row for step 4 (build log docs/geodesic/sorry_notes/reorg_build4.log) and a
"Step 4 notes" section listing moved/new declarations and the line counts of touched files.
Never commit or push.

## Notes carried over from steps 2–3 (current state)
- `oracleNatComplexity_le_of_decoder` (A explicit) is now in `Oracle/PrefixComplexity/Decoders.lean`;
  `partrecIn_mono` in `Oracle/Closure.lean`; `IsREIn.exists_partrecIn_choice` in `Oracle/Search.lean`;
  `IsComputablyCompactFamilyIn.subset_ceOpen_isREIn`, `isCeOpenFamilyIn_ball`, `IsCeOpenFamilyIn.union/comp`
  in `ComputableMetric/{Compact,CeOpen}.lean`; `isREIn_fin_uniform` in `Oracle/Closure.lean`.
- `precisionComplexityNat_anti`, `precisionComplexityNat_le_of_dist_lt` are still in
  `Geodesic/OrbitToLocation.lean` (move them to Charging.lean).
- Deferred to step 7 (do not do now): Points.lean imports `Dynamics/BowenBalls` for
  `birkhoff_computableIn_lt/gt`, `computable_rat_inv_two_pow`, `IsComputableRealFamilyIn.comp`;
  those generic lemmas should move to `Oracle/Closure.lean`.
