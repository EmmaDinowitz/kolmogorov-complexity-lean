# Notes on Chapter D (`Geodesic/Localization.lean`)

Status (wave 2): zero errors, **no `sorry`** (checked against the fresh Chapter B/C oleans compiled
out of tree; the final serial build must rebuild B, C before D).

Changes made in wave 2 (as instructed):
- `shadowSet (ρ : ℝ) (r : ℚ) (kp i T kq)` / `shadowSetBackward` now use `G.Kplaque r (E.pIdx kp)`
  (resp. `Kplaque' r`); decoder inputs are `ℕ × ℚ × ℕ × ℕ × ℕ × ℕ` = `(kp, r, i, T, kq, p)`
  (`Fin nBoxes × …` for the projection decoder); the former closure hypothesis is replaced by
  `0 < r ∧ (r : ℝ) ≤ ε₀` in `shadowSet_subsingleton`, `localization_decoder(_proj/_backward)`,
  `isComputablePointIn_of_shadowSet`, `shadowSetBackward_subsingleton`; `shadowSet_compl_ceOpen`
  and `shadowSetBackward_compl_ceOpen` carry `r` in the index (it does not enter `O`).
- Generic decoder `decoder_of_compl_ceOpen` now takes `K : ℕ × ℚ → Set X` and its hypotheses only
  at positive radii (needed because `Kplaque_cc` is the `if 0 < r then … else ∅` family).
- New helpers: `GeodesicReconstructionData.Kplaque_subset_closure_plaque`,
  `Kplaque'_subset_closure_plaque` (from `Kplaque_spec`, item 8.1),
  `shadowSet_subset_family`, `shadowSetBackward_subset_family`.
- `shadowSetBackward_subsingleton` now uses `G.plaque_expansivity_backward` directly (the
  earlier local `sorry` is gone).
