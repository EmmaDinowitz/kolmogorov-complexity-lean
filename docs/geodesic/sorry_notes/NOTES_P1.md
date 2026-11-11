# NOTES_P1: Riccati.lean (Part 1), first half (everything before "### The rates `lamU` and `lamS`")

Scope after the coordinator's change: only the sorries before the lamU/lamS section. All helpers are
private and prefixed `aux1_`. One import was added: `Mathlib.Analysis.ODE.ExistUnique` (it brings in
Picard–Lindelöf and Grönwall). No statement, definition or name was changed.

## Status: all first-half sorries are filled except `logDerivTo_anti_pole`, which is FALSE as stated
`lake env lean`: 0 errors. 26 sorry warnings: the 25 second-half theorems (left alone) and
`logDerivTo_anti_pole`.

### FALSE: `logDerivTo_anti_pole`
Stated: `t < s₁ → s₁ ≤ s₂ → logDerivTo v s₂ t ≤ logDerivTo v s₁ t`.
Counterexample: `K ≡ 0` (for example a one-point space, trivial flow). Then `jacobiTo v s t = s - t`,
`jacobiTo' = -1`, and `logDerivTo v s t = -1/(s - t)`. With `s₁ = 1`, `s₂ = 2`, `t = 0` the claim
reads `-1/2 ≤ -1`. In general `logDerivTo v s t` INCREASES with `s` (consistent with the module doc:
"lamS = minus the increasing limit of logDerivTo v T 0").
Proposed correction (proved in the file as `aux1_logDerivTo_mono_pole`):
  `theorem logDerivTo_mono_pole (v : X) {s₁ s₂ t : ℝ} (h₁ : t < s₁) (h₂ : s₁ ≤ s₂) :
      C.logDerivTo v s₁ t ≤ C.logDerivTo v s₂ t`
(proof: `logDerivTo_eq_reverse` and `logDerivFrom_mono_pole` for `C.reverse`).

## Groups done (one-line proof ideas)
- orbitK continuity/flow, `reverse` fields (`|-s| = |s|`), `reverse_orbitK` (rfl), `Kbound` (compact
  range is bounded above; an empty `X` gives `sSup ∅ = 0`).
- Linear ODE helpers (`aux1_linField`, i.e. `(y, y') ↦ (y', q t y)` with Lipschitz constant `max 1 M`):
  uniqueness through `ODE_solution_unique_univ`; existence on `[s-n, s+n]` from `IsPicardLindelof` for
  the system with the state clamped to a box of radius `R = ‖x₀‖ e^{K' n}`, followed by forward and
  backward Grönwall bounds showing the clamp is never active; global existence by gluing the interval
  solutions (they agree on overlaps by `ODE_solution_unique_of_mem_Icc`).
- Linearity, Wronskian (derivative 0, `is_const_of_deriv_eq_zero`), `comp_add`, `reverse` (generic
  `aux1_isJacobiSolution_neg` for any pair of reversed potentials).
- `deriv_monotoneOn_of_nonneg`: `y'' = -K y ≥ 0` on the convex set `I`. `pos_of_zero_at`: continuous
  induction (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`) on `{0 ≤ y ∧ 1 ≤ y'}`, then
  `y t ≥ t - s`.
- Flow and reversal identities for `jacobiFrom/jacobiTo/logDeriv*`: uniqueness applied to the shifted
  or reversed solution (`aux1_jacobiFrom_flow`, `aux1_jacobiTo_eq` give `y` and `y'` together).
- Riccati equation (`aux1_hasDerivAt_div`: the quotient rule plus the Jacobi equation).
- Sturm: `aux1_logDerivFrom_sub_eq`: `u_{s₂}(t) - u_{s₁}(t) = y₁(s₂)/(y₁(t) y₂(t))` (Wronskian
  evaluated at `s₂`); this is ≥ 0 and, by `aux1_logDerivFrom_sub_le`, ≤ `1/(t - s₂)`. With
  `s₂ = -T`, `t = 0` this gives the uniform estimate `0 ≤ u_T(0) - lamU ≤ 1/T`, useful for the second
  half (limits and Dini/uniform continuity of `lamU`).
- Comparison bound `logDerivFrom_le`: Wronskian of `y` with `z(r) = (r-s) e^{Λ(r-s)}`, which has
  `z'' ≥ Λ² z ≥ -K z` and `z'/z = 1/(r-s) + Λ` exactly (so no `coth` and no case `Λ = 0`).
  `neg_logDerivTo_le` follows by reversal.
- `continuous_logDerivFrom`: `dist_le_of_approx_trajectories_ODE` on `[s, t]`, where the solution
  for `w` is an approximate solution for `w₀` with error `sup|K_w - K_{w₀}| · e^{K'(t-s)}` (uniform
  closeness from `Continuous.tendstoUniformly` on `X × Icc s t`, and a Grönwall a priori bound),
  together with continuity of `gronwallBound` in `ε`. `continuous_logDerivTo` follows by reversal.

## Helpers available to the second half
`aux1_sub_le_jacobiFrom` (`t - s ≤ jacobiFrom v s t`), `aux1_jacobiFrom_monotoneOn`,
`aux1_logDerivFrom_sub_le`, `aux1_hasDerivAt_div`, `aux1_monotoneOn_of_hasDerivAt`,
`aux1_abs_neg_orbitK_le`, `aux1_isJacobiSolution_neg`, `aux1_logDerivTo_mono_pole`.
