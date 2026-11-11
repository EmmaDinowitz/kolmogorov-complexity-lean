# Chapter B (`KolmogorovMathlib/PointToSet/Geodesic/GeometricData.lean`): remaining sorries

## `flow_shift_eq_of_mem_plaque_u`

- **Status:** left as `sorry`.
- **Reason:** not derivable from G1–G12. No field relates a strong unstable plaque to the
  flow direction. The only uniqueness statement available is the `lps` uniqueness clause
  `z ∈ W .u v → dW .u v z < κδ → z ∈ W .cs w → dW .cs w z < κδ → z = bracketS v w`; applying
  it with `v := p`, `w := y`, `z := φ s y` would need a bound on `dW .cs y (φ s y)` (a time
  shift stays `cs`-close to the point), and no field bounds the leaf pseudometric of a time
  shift. Flow boxes (`τ_unique`) only concern the section `D`, and `expansive` produces a
  time shift rather than excluding one.
- **Proposed fix:** new field (G3'), "strong plaques are transverse to the flow", e.g.
  `plaque_u_transverse : ∀ Q, IsCompact Q → Q ⊆ Singᶜ → ∃ r > 0, ∃ ε₀ > 0, ∀ p ∈ Q,
  ∀ y ∈ W .u p, dW .u p y < ε₀ → ∀ s, |s| ≤ r → φ s y ∈ W .u p → dW .u p (φ s y) < ε₀ →
  φ s y = y` (the theorem is then immediate), or the simpler pointwise field
  `dW_cs_flow_le : ∀ x s, |s| ≤ 1 → dW .cs x (φ s x) ≤ V * |s|` (together with `W_cs_eq`,
  the `lps` uniqueness clause then gives the theorem).

## `plaque_expansivity`

- **Status:** partially proved; one inner `sorry` remains, namely the hypothesis
  `hshift : ∃ ε₁ > 0, ∀ p ∈ Q, ∀ y ∈ closure (plaque .u ε₁ p), ∀ s, |s| ≤ 2 * rExp →
  φ s y ∈ closure (plaque .u ε₁ p) → φ s y = y`
  at the top of the proof. Everything else is done: regularity of the closed plaques (via
  `IsCompact.exists_thickening_subset_open` and `dist_le_CLeaf_mul_dW`), backward control
  on the closed plaque (nonexpansion `dW_u_flow_le` + `dist_le_CLeaf_mul_dW` on the open
  plaque, then passage to the closure through the closed set of controlled pairs in
  `X × X`, which avoids any continuity of `dW`), `expansive` to get `z = φ s y`, and
  `hshift` to conclude.
- **Why `flow_shift_eq_of_mem_plaque_u` does not suffice even as a black box:**
  (i) it speaks about the open plaque, while the statement needs points of
  `closure (plaque .u ε₀ p)`; `closure (plaque .u ε₀ p) ⊆ plaque .u ε₁ p` for some
  `ε₁ > ε₀` is not derivable (leaves are not known closed, `dW` is not known continuous or
  lower semicontinuous); (ii) its shift bound `r` depends on `Q`, whereas `expansive`
  only yields `|s| ≤ 2 * rExp` with `rExp` a fixed field, and a small `dist y (φ s y)`
  does not bound `s` (nearly periodic orbits).
- **Proposed fix:** either a field (G3'') for closed plaques, e.g.
  `closure_plaque_u_subset : ∀ x r, closure {y ∈ W .u x | dW .u x y < r} ⊆
  {y ∈ W .u x | dW .u x y < 2 * r}` (or `IsClosed (W k x)` plus lower semicontinuity of
  `dW k x`), together with the transversality field above stated with shift bound
  `2 * rExp` (or with an added field `rExp_le` tying `rExp` to the transversality scale);
  or restate `plaque_expansivity` with `plaque .u ε₀ p` in place of its closure, in which
  case the present proof goes through verbatim from `flow_shift_eq_of_mem_plaque_u` once
  the `r` vs `2 * rExp` mismatch is settled.

## Resolution (main session)
Added two fields to `GeodesicReconstructionData` (G3'): `plaque_transverse_u` and
`plaque_transverse_s` — over a compact regular set there is a plaque radius `ε₁` such that a time
shift by `|s| ≤ 2 rExp` of a point of a closed strong plaque landing in the same closed plaque is
trivial. With them `plaque_expansivity` and `flow_shift_eq_of_mem_plaque_u` are proved; Chapter B
has no remaining sorry. The stable field is for the backward decoder's uniqueness (not yet used).
