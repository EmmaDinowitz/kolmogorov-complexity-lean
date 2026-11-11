# Chapters F, G, H (`Geodesic/PlaqueNeighborhoods.lean`, `SectionReconstruction.lean`,
# `OrbitToLocation.lean`): remaining sorries

## F: `exact_cover_cs`, `exact_cover_cu`

- **Status:** left as `sorry`.
- **Reason:** false as stated in the degenerate case `C * κ = 0`. With `C = 0` the
  hypothesis `hcomp` forces `bracketS p w = w`, and `hbranch` then forces every point of
  `plaque .cs ε x ∩ ball p h` to equal `bracketS p x`; all hypotheses are satisfiable (e.g.
  `X = Unit`, `L = [x]`, `ε = h = 1`, `C = κ = 0`; a `GeodesicReconstructionData` exists on
  a one-point space with `Sing = ∅`, `lamU = 1`, all leaves `univ`, `dW = 0`, one box), while
  the conclusion `plaque .cs ε x ⊆ ⋃ p ∈ L, ball (bracketS p x) 0 = ∅` fails because
  `x ∈ plaque .cs ε x` for `ε > 0`. The hypotheses `0 ≤ κ`, `0 ≤ C` do not exclude this.
- **Proposed fix:** strengthen `hκ : 0 ≤ κ` to `1 ≤ κ` and `hC : 0 ≤ C` to `1 ≤ C`
  (these are what `exists_cover_hypotheses` supplies: `κ ≥ 1` from `lps`, `C = CLeaf ≥ 1`),
  or just `0 < C * κ`. With that the proof is the intended one:
  for `w` in the plaque pick `p ∈ L` with `dist p w < h`;
  `dist w (bracketS p x) = dist w (bracketS p w) ≤ C * dW .cs w (bracketS p w) ≤ C κ dist p w
  < C κ h` (`hbranch`, `hcomp`, `hleg`, and `C κ > 0` for the last strict step); the second
  containment is `Metric.mem_thickening_iff` with the center `bracketS p x ∈ Wloc .cs x`
  (`hcenters`) at distance `< C κ h`. Same for `cu` with `bracketU x p`.

## F: `proj_mem_plaques`

- **Status:** left as `sorry` (used as a black box by `section_localization` in G, which is
  proved from it).
- **Reason:** not derivable from the fields. `W_cs_eq` gives `φ (τ x) x ∈ W .cs x`, but no
  field bounds the center leaf pseudometric `dW .cs x (φ t x)` of a time shift; `dW` could
  take the value `rLeaf` off the diagonal on `cs/cu` leaves (a model: circle with the
  rotation flow, `W .u = W .cs = W .cu = univ`, `W .s x = {x}`, `dW .u = dW .cu = dist`,
  `dW .cs = rLeaf · [x ≠ y]`, `bracketS v w = w`, `bracketU v w = w`, `lamU = 0`, `lamS = 1`,
  `Sing = ∅`, two boxes with one-point sections), where the `cs`-plaques of radius `≤ rLeaf`
  are singletons and `proj x ≠ x` in general.
- **Proposed fix:** new field "flow displacement bounds the center leaf distance", e.g.
  `dW_center_flow_le : ∀ x (t : ℝ), dW .cs x (φ t x) ≤ |t| ∧ dW .cu x (φ t x) ≤ |t|`
  (or with a constant `V * |t|`). Then `proj_mem_plaques` is immediate:
  `φ (τ x) x ∈ W .cs x` by `W_cs_eq` (`x ∈ W .s x`), and `dW .cs x (φ (τ x) x) ≤ |τ x| < εx`.
  This is the same missing field noted for Chapter B (`flow_shift_eq_of_mem_plaque_u`).

## G: `section_reconstruction`

- **Status:** left as `sorry` (used as a black box by `orbit_to_location` in H, which is
  proved from it together with the bookkeeping lemmas).
- **Reason:** not derivable from the available statements. The search of the program needs
  a point of the section `D_j` certified inside `U^{cs} ∩ U^{cu} ∩ basicBall (c, rV)`; the only
  source of such a point is `z = (box j).proj x ∈ U^{cs} ∩ U^{cu}` (`section_localization`),
  which requires `z ∈ plaque .cs εx x` and `z ∈ plaque .cu εx x`, i.e. the fixed-phase
  condition `|τ x| < εx` and the (unprovable, see above) `proj_mem_plaques`. Two obstacles:
  1. `effective_neighborhoods` (now proved) only asserts `∃ j r εx, 0 < r ∧ 0 < εx ∧ …`: it
     neither provides `x ∈ (box j).U` (required in the conclusion of
     `section_reconstruction` for the same `j`) nor any relation between `εx` and `τ x`. In
     the proof, `εx ≤ r / (2 CLeaf)` with `2r < δ_net(x)` is forced, because the net of
     `net_approx` only covers `closedBall x (r/2)`; so `εx` is small and `|τ x| < εx` cannot
     hold for a general `x` (a finite atlas has `|τ_j x|` bounded below away from the
     sections).
  2. Even granting `|τ x| < εx`, `z ∈ plaque .cs εx x` needs a bound on `dW .cs x (φ t x)`
     (missing field, see `proj_mem_plaques`).
  The alternative of projecting an arbitrary certified point `y ∈ U^{cs} ∩ U^{cu}` to the
  section by the represented `proj` fails for the same reason: showing
  `proj y ∈ thickening (C₂ E) (Wloc .cs x)` requires the leaf pseudometric along flow lines.
- **Proposed fix:** (i) add the field `dW_center_flow_le` (see `proj_mem_plaques`);
  (ii) strengthen the conclusion of `effective_neighborhoods` to
  `∃ j r εx, x ∈ (box j).U ∧ |(box j).τ x| < εx ∧ …`, which in turn requires the covering
  construction to produce neighborhoods of flow-saturated plaques (e.g. cover
  `plaque .cs εx' x` for a small `εx'`, then saturate the output lists by the represented
  flow `φ q` over a rational grid `|q| ≤ aMax`, using `W_cs_eq` and the new field to show the
  saturation contains `plaque .cs (εx' + aMax) x`), or (iii) restate
  `section_reconstruction` with the output within `C₃ max (E₊, E₋)` of a point of
  `D_j ∩ U^{cs} ∩ U^{cu}` instead of `proj x`. With (i)–(ii) the proof is the assembly
  described in the docstring: `effective_neighborhoods`, `transverse_estimate` +
  `exists_basicBall_code` for `(c, rV)`, the enumeration of `isREIn_secPt_mem`
  (`relative_enumeration`) searched by `Nat.rfindOpt`, `exists_secPt_mem` for
  termination, `section_localization` for the distance bound, and rounding of
  `secPt j k` by `secPt_names` to precision `max (Rp, Rm)`.

## Resolution (main session)
- `exact_cover_cs/cu`: hypotheses strengthened to `1 ≤ κ`, `1 ≤ C`; proved.
- `proj_mem_plaques`: fields G3'' `dW_cs_flow_self`, `dW_cu_flow_self` (`dW .c* x (φ t x) ≤ |t|`)
  added to `GeodesicReconstructionData`; proved from them and `W_cs_eq`/`W_cu_eq`.
- `section_reconstruction` (fixed-phase problem): accepted as the SECOND design item. The fixed
  finite atlas cannot guarantee `|τ_j x| < εx` with `εx ≲ r/(2 CLeaf)`. Planned fix: localization
  data carry a rational time shift `s`, the section is `φ s '' (box j).D` (a translated box, still
  a `FlowBox`), chosen so that `|τ x + s| < εx`; G11 is restated for translated boxes and the
  effective data for their `τ`/`proj` follow from the represented flow. `orbit_to_location`'s
  conclusion then reads `K^A_{C𝓡}(φ t₀ x)` with `|t₀| < εx` instead of `(box j).proj x`. Chapters
  G, H, I statements change accordingly; the proofs already written are reusable.


## Wave 2 (shifted sections): status update for G and H

### G — all sorries closed
- `section_reconstruction` is PROVED with the restated (shifted-section) statement, see below.
  The previous obstruction (fixed phase) is resolved by the rational shift `s` and the new fields
  `dW_cs_flow_self`, `dW_cu_flow_self` (B); `proj_mem_plaques` (F) is no longer used anywhere in
  G/H/I.
- Restated: `isREIn_secPt_mem` (shifted point `φ s (secPt j k)`, input
  `(Fin nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ)`), `section_localization`
  (hypotheses `φ (-s) x ∈ (box j).U`, `|τ (φ (-s) x)| < εx`, `V'`/`htr` on `φ s '' D`;
  conclusion about `Ω = Ucs ∩ Ucu ∩ φ s '' D ∩ V'`), `exists_secPt_mem` (for `z ∈ φ s '' D`,
  gives `k` with `φ s (secPt j k) ∈ O`), `section_reconstruction` (program input
  `Fin nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ`, localization data `(j, s, c, rV, r)`,
  hypothesis `φ (-(s:ℝ)) x ∈ (box j).U`, conclusion
  `dist (ι q) (φ s (proj (φ (-s) x))) ≤ C₃ * max E₊ E₋`).
- New private helpers (proof-only): `isREIn_secPt_mem_basicBall` (the old uniform unshifted
  membership test), `isREIn_shift_mem_basicBall` (shifted membership through the sound/complete
  relation of `E.flow_represented`), `isREIn_shift_round` (the rounding test).
- ⚠ Design wart to be removed when F is adjusted: `effective_neighborhoods` (F) does not export
  `x ∈ (box j).U` for its box `j₀`, and the box used for the section (`j`, with
  `φ (-s) x ∈ U_j`) may differ from `j₀`. The program therefore reads `j₀` from the code
  `c = Nat.pair c' (Encodable.encode j₀)` (`c'` is the ideal center of the neighborhood
  `basicBall (c', rV)`). Cleaner fix: add `x ∈ (G.box j).U` to the conclusion of
  `effective_neighborhoods` (true in its proof: `closedBall x ℓ ⊆ innerBox j ⊆ U_j`); then
  `recon` can use the input `j` for both purposes and `c` is just the center.
- Still relevant from wave 1: `exact_cover_cs`/`exact_cover_cu` and `proj_mem_plaques` in F are
  untouched (not mine); `proj_mem_plaques` is now provable from `dW_cs_flow_self` with
  `|τ x| < εx` as hypothesis.

### H — all sorries closed, statements reshaped
- `orbit_to_location`, `orbit_to_location_log`, `orbit_to_location_regU`,
  `orbit_to_location_lyapunov`: the `∃ j, x ∈ (box j).U ∧ … precisionComplexityNat P A
  ((box j).proj x) …` is replaced by `∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧ … precisionComplexityNat P A
  (G.φ t₀ x) …` (quantified after `x ∈ Reg`, before `ε, C, c₀`; in `_lyapunov` after the two
  `Tendsto` hypotheses). `t₀ = τ_j (φ (-s) x)`, `|t₀| ≤ aMax` by `abs_τ_le_aMax`.


## Wave 3 (final adaptation to E/F): G and H
- `section_reconstruction` now takes `{Px : Set X} (hPx : IsCompact Px) (hPxR : Px ⊆ G.Reg)` after
  `(hPmR : Pm ⊆ G.Reg)` and concludes `∀ x ∈ Px` (passed to `effective_neighborhoods`); the
  exported box membership `x ∈ (G.box j).U` of `effective_neighborhoods` is used for the
  section, so the pair-encoding of `c` is gone: `c` is just the ideal center of the coded
  neighborhood `basicBall P (c, rV)`. The wave-2 "design wart" entry above is obsolete.
- H statements unchanged. `orbit_to_location` obtains `ε₀, Q` from `section_reconstruction` with
  `Px := ∅` (only their properties `Pp ∪ Pm ⊆ interior Q`, `Q ⊆ Reg` are needed) and, for each
  `x`, applies `section_reconstruction` again with `Px := {x}`, discharging its plaque hypothesis
  by `G.smallPlaques`; the `G.SmallPlaques Q ε₀` hypothesis of the H statements is therefore
  unused (kept for statement stability).
- G, H, I: 0 errors, 0 sorries (checked against a mirror of out-of-tree oleans rebuilt from the
  current A–F sources).
