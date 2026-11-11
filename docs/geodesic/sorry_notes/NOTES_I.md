# Notes I (Geodesic/UpperBound.lean)

## Proved
`ControlledReturns.mem_Reg`, `controlledReturns_of_real`, `PositiveRates.exists_linear`,
`birkhoff_uPlus_bounds`, `birkhoff_uMinus_bounds`, `exists_stopping_times`, `return_adjustment`,
`limsup_comp_le_of_tendsto_atTop`, `liminf_nhdsWithin_le_liminf_seq`, `sectionPoint_upper`,
`sectionPoint_mixed`, `flow_coordinate_proj`, `main_pointwise`, `main_set`,
`bsPointToSet_cone_forward`, `bsPointToSet_cone_backward`.

Private helpers added (proof-only additions, no statement changed):
`exists_linear_of_lowerBirkhoffAverage_pos` (positivity of the `EReal` lower average gives the
eventual linear bound directly; Chapter A has no backward version of
`exists_linear_lower_bound_of_pos` for `finv`/`unitPotentialBackward`, so neither direction uses
Chapter A), `birkhoffSum_bounds_of_le`, `stopping_time_aux` (one-sided stopping times, shared by
`exists_stopping_times` and `mixed_core`), `tendsto_log_geometric_ratio`, `precision_chain_aux`,
`ennreal_limsup_add_le` (subadditivity of `limsup` in `ℝ≥0∞` along `atTop`; the library's
`ENNReal.limsup_add_le` needs `CountableInterFilter`, which `atTop` on `ℕ` is not), `mixed_core`
(the analytic core of `sectionPoint_mixed`, `set_option maxHeartbeats 1600000`).

## `exists_stopping_times` — provable only with `N₀ := 0` and a smaller `lam`
As stated, the bound `S_{n⁺(p)} u⁺ ≤ p + ρ n⁺(p) + Λ' + ρ` fails for small `p` if `n⁺(p)` is
defined as the least `n ≥ N₀` (the minimality argument does not apply when `n⁺(p) = N₀`, and
`S_{N₀}` can exceed `p + ρ N₀ + Λ' + ρ`). The proof therefore returns `N₀ = 0`, defines `n⁺(p)` as
the least `n` (no threshold) with `p ≤ S_n - ρ n`, and shrinks the slope to
`lam = min lam₀ (2 / (N₀' + 1))` so that `2p/lam ≥ N₀' + 1` for `p ≥ 1` (the upper bound
`n⁺(p) ≤ 2p/lam + 1` then follows). All downstream statements only use the exported `lam, N₀`.

## `precision_chain` — UNPROVABLE as stated (sorry left)
For `c` large and `ρ` close to `lam/2` one has `θ = 2ρ(c-1)/lam ≥ 1`. Then the two conclusions
`∀ p, -logb 2 (δ p) ≤ (1-θ) p + c₀` and `Tendsto δ atTop (𝓝 0)` are contradictory (the first
gives `δ p ≥ 2^{-c₀}`). Proposed fix: add the hypothesis `2 * ρ * (c - 1) < lam` (i.e. `θ < 1`)
after `ρ < lam / 2`. The private lemma `precision_chain_aux` is exactly this corrected statement,
fully proved, and `sectionPoint_upper` uses it (with `c = 1 + ρ`, so `θ = 2ρ²/lam < 1`).

## `orbitToLocationEstimate_of_smallPlaques` — unprovable from Chapter H as stated (sorry left)
`orbit_to_location` produces the box `j` AFTER `Pp, Pm, ρ` (inside the existential for each
triple), whereas `OrbitToLocationEstimate` requires one `j` per point, valid for all compact
regular endpoint sets and all losses. There is no way to exchange the quantifiers (finitely many
boxes, uncountably many triples; the estimate for one box does not transfer to another box at
fixed scale within `O(1)`). Proposed fix: state `orbit_to_location` with
`∀ x ∈ G.Reg, ∃ j, x ∈ (G.box j).U ∧ ∀ Pp Pm ρ, ∃ ε₀ Q, ... ∃ ε C c₀, ...` — the proof sketch
("take the decoder of `section_reconstruction` with the localization built in") works for any
box containing `x`, so `j` can be chosen first (e.g. from `exists_box_mem`).

## `sectionPoint_mixed` — proved, but NOT by the blueprint's route
The blueprint pads the forward description from `n_k` to `T⁺_k ∈ [n_k, c n_k]` with
`orbit_extension_normalized`, at cost `(c-1) n_k ⌈log₂ N(ε')⌉`, and lets `c → 1` before `q → ∞`.
This does not work: the radius `ε = ε(ρ, P^±(c))` of the orbit-to-location estimate depends on the
return sets, hence on `c`, so `N(ε')` is not fixed as `c → 1`. Fix used here (`mixed_core`): take
the forward return in `[n_k / c, n_k + c]` (controlled returns applied at `m = ⌈n_k / c⌉₊`) and
pad only by the CONSTANT `⌈c⌉₊` steps with `orbit_extension` (pointwise form); the padding cost is
`O(log n_k)` and disappears, while the loss in the scale is `Λ'(c-1) n_k` (monotonicity
`S_{T} ≥ S_n - Λ'(n - T)`), absorbed in `ϑ = 2(ρ + Λ')(c-1)/λ̲`. The liminf-realizing sequence is
`exists_seq_tendsto_liminf`; the final bound is `liminf ≤ limsup` and then as in
`sectionPoint_upper`. The second component of the `min` is the same lemma with the two sides
swapped (`min_comm`, `add_comm`), so `mixed_core` is stated for abstract two-sided data.

## `flow_coordinate` — NOT PROVED (sorry left); blocked by a missing library lemma
Everything is available except one complexity bound. The decoder (input `(i, k, m)`: search, via
`relative_enumeration` applied to the RE relation of `E.flow_represented` at the rational
`q = k 2^{-m} - (a+1)`, for a basic ball `c` of radius `< δ/2` containing `φ q (ι i)`, output its
center) is `PartrecIn`, and `oracleNatComplexity_le_of_decoder` (Chapter H) gives
`K^A_{(L'+V+1)δ}(x) ≤ K^A_δ(z) + K^A(0) + oraclePairComplexity A k m + c`. The library bounds the
time code only by `oracle_tuple_bounds_overhead`: `K(k, m) ≤ K(k) + 2 log₂(m+1) + c`, and there is
NO bound `K(k) ≤ log₂(k+1) + O(log log k)` (nor `oracleComplexity A x ≤ x.length + O(log)`); with
`oraclePairComplexity_le_log` one only gets `2 log₂(k+1) ≈ 2m`, i.e. `Dim x ≤ 2 + Dim z`.
Missing lemma (belongs in `Oracle/PrefixComplexity`): 
`∃ c, ∀ n, (oracleNatComplexity A n : ℝ) ≤ Real.logb 2 (n+1) + 2 * Real.logb 2 (Real.logb 2 (n+1) + 1) + c`,
provable from `oracle_kraftChaitin_bound` with the computable request stream
`req n := some (natBits n, (natBits n).length + 2 * (natBits (natBits n).length).length + 3)`
(Kraft mass `≤ ∑_ℓ 2^{-2 log ℓ - 3} ≤ 1`). Remaining analytic steps once that lemma exists:
Lipschitz bound `dist (φ s y) (φ s y') ≤ L^{⌈|s|⌉} dist y y'` by iterating `lipschitz_unit`,
`speed_unit` for `dist (φ q z) (φ (-t₀) z) ≤ V δ`, `staticPointDimensions_attained` for the
realizer `i`, `precisionComplexityNat_le_of_dist_lt`, then `dimension_along_scales_upper` /
`dimension_along_scales` with `δ_m = (L'+V+1) 2^{-m}` (ratio condition from
`tendsto_log_geometric_ratio`) and `neg_logb_dyadicRadius`, and the `ℝ≥0∞` bookkeeping as in
`sectionPoint_upper` (`m/(m - c') → 1`).

## Remaining sorries
`orbitToLocationEstimate_of_smallPlaques`, `precision_chain` (both unprovable as stated, see
above), `flow_coordinate` (missing library lemma, see above).


## Wave 2 (interface with per-parameter section point): status update

- `OrbitToLocationEstimate G P A` is now
  `∀ x ∈ Reg, ∀ Pp Pm, IsCompact Pp → Pp ⊆ Reg → IsCompact Pm → Pm ⊆ Reg → ∀ ρ : ℚ, 0 < ρ →
  ∃ t₀, |t₀| ≤ G.aMax ∧ ∃ ε > 0, ∃ C > 1, ∃ c₀ : ℕ, ∀ Tp Tm, φ Tp x ∈ Pp → φ (-Tm) x ∈ Pm →
  precisionComplexityNat P A (φ t₀ x) (C * combinedScale ρ Tp Tm x) ≤ … + c₀`.
- `orbitToLocationEstimate_of_smallPlaques`: PROVED from the new H statement. The hypothesis
  `hsmall : ∀ Q, IsCompact Q → Q ⊆ Reg → ∀ ε₀ > 0, SmallPlaques Q ε₀` is still there; it is to be
  discharged by the forthcoming `G.smallPlaques` (C/D/E worker) after which the hypothesis can be
  dropped (one-line change: replace `hsmall Q hQ hQR ε₀ hε₀` by `G.smallPlaques …`).
- `precision_chain_aux`/`precision_chain`: statement changed accordingly: `∃ lam N₀, ∀ c ρ …,
  ∃ t₀, |t₀| ≤ aMax ∧ ∃ ε Tp Tm δ c₀ p₀, … precisionComplexityNat P A (φ t₀ x) (δ p) …`
  (the box `j` is gone; the section point depends on `(c, ρ)`).
- `sectionPoint_upper` / `sectionPoint_mixed`: now statements about `x`, with the extra arguments
  `{B} (E : EffectiveGeodesicData G P B) (hBA : charOracle B ≤ᵀ charOracle A)`:
  `(staticPointDimensions P A x).2 ≤ 1 + D⁺ + D⁻` and
  `(staticPointDimensions P A x).1 ≤ 1 + min (d⁺ + D⁻) (D⁺ + d⁻)`. In both proofs
  `flow_coordinate` is applied inside the parameter loop (claim A), before the limits
  `q → ∞`, `ρ → 0`, `c → 1`. `mixed_core` was generalized (its `hest` yields the section point
  `z` together with `dim x ≤ 1 + dim z`; conclusion `dim x ≤ 1 + (d₁ + D₂)`).
- `flow_coordinate`: PROVED (statement unchanged; now `EffectiveGeodesicData.flow_coordinate`
  stated inside `section limits`, so it takes `P` explicitly: `E.flow_coordinate P hBA ht₀`).
  Ingredients: `E.flow_represented` (sound/complete relation) for the decoder on inputs
  `(i, 0, k, m)` with the dyadic time `q = k 2^{-m} - N`, `N = ⌈a⌉₊ + 1`;
  `oracleNatComplexity_le_of_decoder`, `oracle_tuple_bounds_overhead`,
  `oracleNatComplexity_le_log_add_loglog` (Chapter A, new); Lipschitz bound `L^N` over
  `|s| ≤ N` by induction from `lipschitz_unit`; `speed_unit`; `dimension_along_scales(_upper)`
  along `2^{-m}` and `(1 + L^N + V) 2^{-m}` (`tendsto_log_geometric_ratio`); `ℝ≥0∞` bookkeeping
  with `ennreal_limsup_add_le` / `Monotone.map_liminf_of_continuousAt`, then `η → 0`.
- `flow_coordinate_proj` kept as a corollary. `main_pointwise` is now just the pair of
  `sectionPoint_upper`/`sectionPoint_mixed`; `main_set` unchanged.
- Chapter I has NO remaining sorries.


## Wave 3
- `orbitToLocationEstimate_of_base {A} (hBA : charOracle B ≤ᵀ charOracle A) :
  OrbitToLocationEstimate G P A` (new, no plaque hypothesis; uses `G.smallPlaques`);
  `orbitToLocationEstimate_of_smallPlaques` kept as a one-line corollary (its `hsmall` is unused).
- UpperBound.lean rechecked against the rebuilt mirror: 0 errors, 0 sorries.
