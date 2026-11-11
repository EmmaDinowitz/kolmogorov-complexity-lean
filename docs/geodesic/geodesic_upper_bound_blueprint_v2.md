# Blueprint v2: pointwise upper bound under controlled regular returns

Second version, written against the Lean modules `KolmogorovMathlib/PointToSet/Geodesic/*.lean`
as they stand after the first filling pass (snapshot: 2026-11-03, three workers still active on
Chapters C, F–G–H and I; the status appendix in Section 9 is regenerated at the end of the run).

Where v1 described the drafts' arguments, v2 describes what is actually formalized: statements as
stated in Lean, with the hypotheses that turned out to be needed, the fields that had to be added,
and the exact shape of what is still open. Status tags:

* **proved** — compiles with no `sorry`;
* **open: program** — a relatively partial recursive search/decoder remains to be built;
* **open: library** — needs a small reusable lemma in the computability layer;
* **open: design** — blocked on the shrinkable plaque family (Section 8.1);
* **field** — a hypothesis of `GeodesicReconstructionData`, verified outside Lean.

The point-to-set framework is cited from `kolmogorov-complexity-lean`
(`Kolmogorov.PointToSet`, Lean 4.35.0). Mathematical sources as in v1 (OTL, MAIN, PO, UEL, LBF).

---

## 0. Decisions in force

**From v1 (D1–D7).** Discrete time through the time-one map `f = φ 1` and `finv = φ (-1)`;
unit-time integrated potentials in bits `u⁺ x = (log 2)⁻¹ ∫₀¹ λᵘ(φ τ x) dτ` (D1, D2); the
library's `staticPointDimensions` and `pointwiseBSDimension` as the pointwise quantities, with the
centred-denominator bridge (D3); every statement for oracles `A` above a base oracle `B` (D4);
geometry as the structure `GeodesicReconstructionData` (D5); integer return times (D6); constants
may depend on the point but never on durations or precision (D7).

**Added during formalization (S1–S8).**

* **S1.** Superscripts are not identifier characters: `Pp, Pm, Tp, Tm, ip, im`; the rate function
  is `lam`.
* **S2.** Finite orbit complexity is the library's `orbitComplexity : ℕ∞` / `orbitComplexityNat`
  (`PointToSet/Pressure/Defs.lean`); Chapter A only adds its properties.
* **S3.** Local products are total functions `bracketS`, `bracketU`; their meaning is the field
  `lps`, quantified over every compact regular set. Branch consistency is a separate field.
* **S4.** The transverse estimate (G11) is stated with the ambient distance on the section; no
  intrinsic section metric exists in the formalization.
* **S5.** Two fields G3' were added: strong plaques are transverse to the flow at the expansivity
  scale (`plaque_transverse_u`, `plaque_transverse_s`). Without them `plaque_expansivity` is not
  derivable from G1–G12 (NOTES_B.md). With them Chapter B is sorry-free.
* **S6.** The orbit-extension lemma has a rational radius `ε : ℚ`: with a real radius the
  membership test of the padding search is not semidecidable (NOTES_A.md). Downstream uses only
  dyadic radii, so nothing else changed.
* **S7.** `Wloc_subset_closedBall_of_small` carries the extra hypothesis `εx ≤ rLeaf` (the
  comparison `dist ≤ CLeaf · dW` holds only on local plaques).
* **S8.** Chapter I is stated for an oracle satisfying the interface `OrbitToLocationEstimate G P A`
  (the conclusion of Chapter H with the box fixed per point). The main theorems are proved from the
  interface. The derivation of the interface from Chapter H is the single remaining design item
  (Section 8.1).

---

## 1. Library declarations used (unchanged from v1, with additions)

| what | declaration | file |
|---|---|---|
| presentation, dyadic radii, Cauchy names, basic balls | `Presentation`, `dyadicRadius`, `IsCauchyName`, `basicBall` | `ComputableMetric/Presentation.lean` |
| computable metric table, represented maps, admissibility | `ComputablePresentationIn`, `IsRepresentedMapIn`, `IsAdmissible`, `realPresentation`, `eval_computable_names` | same |
| relative c.e. predicates and closure toolkit | `IsREIn`, `IsEnumerationIn`, `relative_closure_*`, `relative_enumeration` | `Oracle/Basic.lean`, `Oracle/Universal/Enumeration.lean` |
| oracle complexity and bounds | `oracleNatComplexity`, `oraclePairComplexity`, `oracle_tuple_bounds_overhead`, `oracle_tuple_bounds_composition`, `oracle_monotonicity` | `Oracle/PrefixComplexity/Basic.lean` |
| joins | `oracleJoin`, `oracle_joins`, `oracle_joins_right` | `Oracle/Joins.lean` |
| static dimensions | `precisionComplexity(Nat)`, `normalizedPrecisionComplexity`, `staticPointDimensions`, `_attained`, `_antitone`, `dimension_along_scales(_upper)` | `ComputableMetric/StaticDimensions.lean`, `DimensionAlongScales.lean` |
| Bowen balls, oscillation, finite-scale BS cost | `bowenBall`, `mem_bowenBall_iff`, `bowen_ball_dense*`, `bowenBall_subset_of_le`, `small_scale_oscillation(_birkhoff)`, `finiteScaleBSCost`, `finiteScaleBSCost_le_div`, `finite_scale_min_attained_ratio`, `pointwiseBSDimension_antitone_radius` | `Dynamics/BowenBalls.lean` |
| pointwise BS dimension, Birkhoff averages | `pointwiseBSDimension`, `lowerBirkhoffAverage`, `upperBirkhoffAverage` | `Dynamics/PointwiseQuantities.lean`, `BSDimension/Defs.lean` |
| finite orbit complexity (S2) | `orbitComplexity`, `orbitComplexityNat` | `Pressure/Defs.lean` |
| limit side selector | `LimitSide`, `.choose`, `.timeLimit`, `.timeLimit_mono` | `BSDimension/Defs.lean` |
| Main B and classical principles on cones | `bsPointToSet_cone`, `classicalPointToSet_cone`, `classicalPointToSet_cone_upper`, `metricPackingDimension` | `BSDimension/Upper/PointToSetPrinciple.lean`, `Conformal/Classical/PointToSetPrinciple.lean` |
| normalized slack | `normalized_additive_slack*`, `exists_birkhoffSum_lower_bound` | `Order/NormalizedSlack.lean` |

Mathlib facts that were non-obvious to locate, for whoever continues:
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`,
`intervalIntegral.integral_comp_add_right`, `intervalIntegral.integral_comp_sub_left`,
`intervalIntegral.norm_integral_le_of_norm_le_const`, `Flow.continuous`, `Flow.continuous_toFun`,
`Flow.map_add`, `Flow.map_zero_apply`, `Flow.toHomeomorph`,
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`,
`IsCompact.exists_thickening_subset_open`, `lebesgue_number_lemma_of_metric`,
`Rat.denseRange_cast`, `Nat.floor_le`, `Nat.lt_floor_add_one`, `EReal.exists_between_coe_real`,
`Filter.eventually_lt_of_lt_liminf`, `Filter.le_liminf_of_le`, `Filter.liminf_nat_add`,
`ENNReal.liminf_const_mul_of_ne_top`, `ENNReal.Tendsto.mul_const`, `Function.argminOn`,
`Real.tendsto_pow_logb_div_mul_add_atTop`. Renamed since older Mathlib: `le_or_gt` (not
`le_or_lt`), `Set.sdiff_subset_sdiff_left`, `mul_le_mul_right` for `b ≤ c → a * b ≤ a * c`.

---

## 2. Chapter A — `Geodesic/FlowInterface.lean` (flow-to-map interface)

Definitions: `FlowData` (flow `φ`, unit-time Lipschitz constant `L ≥ 1`, speed bound `V`),
`FlowData.f`, `finv`, `unitPotential`, `unitPotentialBackward`, `accumulatedRate(Backward)`,
`centeredBSCost`.

| node | Lean | status | statement as formalized / proof note |
|---|---|---|---|
| `geo:flow-data` | `iterate_f`, `iterate_finv`, `finv_f`, `f_finv`, `continuous_f`, `continuous_finv`, `dist_f_le`, `dist_finv_le` | proved | induction with `Flow.map_add`; Lipschitz from the field at `s = ±1`. |
| `geo:bowen-flow-compare` | `dist_flow_lt_of_mem_bowenBall(_finv)`, `mem_bowenBall(_finv)_of_dist_flow_lt` | proved | `t = ⌊t⌋₊ + s`, `φ t = φ s ∘ φ ⌊t⌋₊`, unit Lipschitz. Bowen order `n+1` ↔ continuous `[0,n]`, tolerance `L ε`. |
| `geo:unit-potentials` | `continuous_unitPotential(Backward)`, `uniformContinuous_*`, `unitPotential(_Backward)_nonneg`, `_le`, `birkhoffSum_unitPotential(Backward)`, `exp_neg_accumulatedRate_eq_two_zpow`, `abs_accumulatedRate_sub_le`, `lowerBirkhoffAverage_unitPotential_pos_iff`, `exists_linear_lower_bound_of_pos` | proved | parametric integral continuity; `∫₀ⁿ = ∑ ∫_k^{k+1}` with translation; `0 ≤ u ≤ Λ/log 2`; positivity of the `EReal` liminf ⇔ eventual linear lower bound `c · t ≤ S(t,x)`. Headers trimmed to the hypotheses each proof uses (`include hlam0 in`, etc.). |
| `geo:orbit-complexity` (S2) | `orbitComplexityNat_attained`, `_le`, `_mono_order`, `_anti_radius`, `_timeLimit_order_shift`, `_mono_oracle`, `finiteScaleBSCost_le_orbitComplexityNat` | proved | attainment via `Function.argminOn` over a nonempty set of ideal indices (`bowen_ball_dense`, order 0 by `bowen_ball_dense_zero`). |
| `geo:bs-denominator-swap` | `centeredBSCost_timeLimit_le`, `finiteScaleBSCost_timeLimit_le_centered`, `centeredBSCost_timeLimit_mono`, `iSup_centeredBSCost_timeLimit_eq`, `centeredBSCost_timeLimit_le_pointwiseBSDimension` | proved | factor `1 + η p` with `η p = ofReal (ω p / (r/2))`, `ω` from `small_scale_oscillation`, `r` a real strictly below the lower average (`EReal.exists_between_coe_real`); limits via `ENNReal.liminf_const_mul_of_ne_top`, equality of suprema by `ge_of_tendsto`. |
| `geo:orbit-extension` (S6) | `exists_finite_ideal_net` | proved | compactness and density of ideal points. |
|  | `orbit_extension_normalized` | proved from `orbit_extension` | handles the non-cobounded `limsup` case via `Real.sInf_of_not_bddBelow`. |
|  | `isREIn_mem_bowenBall_inter_pullbacks` | open: library | needs (a) a public computable-real-family lemma for `dist (T^[t] (ι i)) (ι m)` (only the private `computable_orbit_distances` exists) and (b) an `IsREIn` closure lemma for a bounded `∀` over a `List` (no list recursion in the `PartrecIn` toolkit). |
|  | `orbit_extension` | open: program | the padding search (first certified `l`), plus a tuple-decompressor complexity bound `K(l) ≤ K(i) + m⌈log₂N⌉ + 2log₂(n+1) + 2log₂(m+1) + c` for an input containing a list of `m` symbols; `oracle_tuple_bounds_composition` covers fixed arity only. |

---

## 3. Chapter B — `Geodesic/GeometricData.lean` (geometric standing data) — sorry-free

Definitions: `LeafKind` (`u s cu cs`), `FlowBox φ` (`U, D, a, τ, proj` with `τ_unique`),
`GeodesicReconstructionData X extends FlowData X`, `Reg`, `plaque`, `Wloc`, `regU`, `regS`,
`uPlus`, `uMinus`, `aMax`.

### 3.1 Fields (hypotheses, verified outside Lean)

| field(s) | content | used by |
|---|---|---|
| G1 `Sing`, `isClosed_Sing`, `Sing_invariant` | closed invariant singular set | `isOpen_Reg`, `Reg_invariant` |
| G2 `lamU lamS`, continuity, `0 ≤ lam ≤ Λ`, `lam_eq_zero_iff` | rates; nonnegativity is load-bearing in `return_adjustment` | A (potentials), I |
| G3 `W`, `dW`, `mem_W`, `W_eq_of_mem`, `dW_self/comm/triangle`, `W_invariant`, `W_cs_eq`, `W_cu_eq`, `rLeaf`, `CLeaf`, `dist_le_CLeaf_mul_dW` | leaves, leaf pseudometrics, plaques, `d ≤ CLeaf·d^*` on local plaques | everywhere |
| G3' `plaque_transverse_u`, `plaque_transverse_s` (S5) | time shifts `|s| ≤ 2rExp` inside a closed strong plaque are trivial, uniformly over compact regular sets | `plaque_expansivity(_backward)`, `flow_shift_eq_of_mem_plaque_u` |
| G4 `dW_s_flow_le`, `dW_u_flow_le` | forward/backward nonexpansion of strong leaf metrics | D, E |
| G5 `leafwise_contraction_s/u` | contraction along a reference orbit with loss `β` | E (`bracket_construction_error`) |
| G6 `Cc`, `center_leg_cs/cu` | short centre legs stay short | E |
| G7 `bracketS`, `bracketU`, `lps` | local products with leg bounds and uniqueness near every compact regular set | E, F |
| G8 `branch_consistency` | `[p,y]_s = [p,x]_s` on centre-stable plaques | F |
| G9 `rExp`, `expansive` | flat-strip expansivity on `Reg` | D |
| G10 `periodic`, density, periods, `Kplaque`, `Kplaque'`, their specs | marked periodic points with compact plaques | C, D, E |
| G11 `transverse_estimate` (S4) | `dist y z ≤ Ltr · max(infDist y W^{cs}_loc, infDist y W^{cu}_loc)` on `D ∩ V` | G |
| G12 `nBoxes`, `box`, `innerBox`, `isOpen_innerBox`, `closure_innerBox_subset`, `innerBox_cover` | finite flow-box atlas | C, E, G |

### 3.2 Theorems (all proved)

`isOpen_Reg`, `Reg_invariant` (via `Flow.toHomeomorph` and `Set.image_compl_eq`),
`mem_Reg_of_lamU_pos/lamS_pos`, `isCompact_regU/regS`, `regU/regS_subset_Reg`,
`uniformContinuous_lamU/lamS`, `uPlus_props`, `uMinus_props`, `mem_W_flow`, `dist_lt_of_mem_Wloc`,
`exists_lps_regU/regS` (G7 specialized; this is v1's `geo:lps-from-compact`),
`bracketS_mem_Wloc_cs` (δ shrunk to `min δ (rLeaf/κ)`),
`plaque_expansivity` and `plaque_expansivity_backward` (closed plaques are regular by
`IsCompact.exists_thickening_subset_open`; backward/forward control passed to the closure through
the closed set of controlled pairs in `X × X`, so no continuity of `dW` is needed; `expansive`
yields a shift; G3' kills it), `dist_flow_neg_le_of_mem_W_u`, `flow_shift_eq_of_mem_plaque_u`,
`lamU_flow_close_of_cs_leg`, `lamS_flow_close_of_cu_leg`, `accumulatedRate_close_of_cs_leg`
(`intervalIntegral.integral_sub` + `norm_integral_le_of_norm_le_const`),
`dW_u_flow_neg_le_of_accumulatedRate`, `dW_s_flow_le_of_accumulatedRateBackward` (G5 at
`v = φ(±T) a`, change of variables `integral_comp_sub_left`), `exists_box_mem`, `proj_spec`,
`abs_τ_le_aMax`.

---

## 4. Chapter C — `Geodesic/EffectiveData.lean` (effective standing data)

Notions added to the library layer: `IsComputablePointIn`, `IsRepresentedFamilyIn`,
`IsRepresentedOnIn`, `IsComputablyCompactIn`, `IsComputablyCompactFamilyIn`, `IsCeOpenIn`,
`IsCeOpenFamilyIn`. Structure `EffectiveGeodesicData G P B` (items 1–5 of v1).

Proved so far (worker still active): oracle monotonicity for all notions, `isComputablePointIn_ι`,
`IsComputablePointIn.map`, `IsRepresentedFamilyIn.apply`, `.names`, `IsRepresentedMapIn.onSubset`,
`IsRepresentedOnIn.map`, `IsComputablyCompactIn.subset_ceOpen_isREIn`, `isREIn_mem_basicBall`,
`isCeOpenFamilyIn_ball`, `f_represented`, `finv_represented`, `isAdmissible_f/finv/rates`,
`orbit_approximants(_backward)`, `birkhoff_uPlus/uMinus_computable`, `isComputablePointIn_pIdx`,
`periodic_orbit_names`, `exists_pIdx_near`, `exists_innerBox_isREIn`, `isComputablePointIn_proj`,
`isComputablePointIn_secPt`, `mono`, `mono_pIdx`, plus helper lemmas the worker added
(`IsREIn.exists_computableIn_choice`, `exists_names_of_ballRel`, `isREIn_mem_basicBall_of_name`,
`computableIn_table_row`, `isOpen_eq_biUnion_basicBall`, `exists_effectiveGeodesicData_of_nonempty`,
`IsCeOpenFamilyIn.inter_of_presentation`).

Open at the snapshot: `IsCeOpenFamilyIn.inter` (the unconditional form; the variant assuming a
computable presentation is proved), `uPlus_represented`, `uMinus_represented` (effective quadrature
of a represented real along the represented flow), `exists_effectiveGeodesicData` (coding dense
enumerations, compactness certificates and box data into one oracle; a conditional form exists).

---

## 5. Chapter D — `Geodesic/Localization.lean` (effective localization)

| Lean | status | note |
|---|---|---|
| `exists_subset_ball_of_iInter_eq_singleton` | proved | Cantor via `nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` on `K n \ ball`. |
| `dist_flow_le_of_forall_rat` | proved | closed condition, `Rat.denseRange_cast`. |
| `dist_flow_le_of_integer_samples` | proved | `⌊t⌋₊`, unit Lipschitz. (Hypothesis `0 ≤ ρ` turned out unused; kept as `_hρ`.) |
| `localization_uniq_of_expansive` | proved | G9 + the rational-to-real lemma. |
| `shadowSet`, `dist_flow_le_of_mem_shadowSet` | proved | integer samples `≤ 2ρ`, then `2Lρ`. |
| `shadowSet_subsingleton` | proved | from `plaque_expansivity`. |
| `shadowSet_compl_ceOpen` | open: library | finite conjunction of strict inequalities on computable reals; needs C's wrappers for the ideal orbit at integer times, the periodic orbit, and the candidate. |
| `localization_core`, `localization_decoder`, `localization_decoder_proj`, `localization_decoder_backward` | open: program | the certified search (Section 8.2). Correctness and termination inputs are all proved; the backward one uses `plaque_expansivity_backward`. |
| `isComputablePointIn_of_shadowSet` | open | immediate from the decoder. |

---

## 6. Chapter E — `Geodesic/BracketApprox.lean` (local products from orbit data)

| Lean | status | note |
|---|---|---|
| `scalePlus`, `scaleMinus`, `_pos`, `_mono_loss`, `scalePlus_eq_exp`, `two_zpow_neg_le_scalePlus` | proved | `E₊(ρ) = 2^{-(S_T u⁺ - ρT)} = exp(-(∫λᵘ - ρ log 2 · T))`. |
| `SmallPlaques Q ε₀` | definition | side condition for decoders (Section 8.1). |
| `bracket_construction_error` | proved | `dist(φ(-T)[φT a, q]_s, a) ≤ CLeaf κ_P δ' · E₊(ρ)`: G5 along `a` (loss `β = ρ log 2/2`), rate comparison along the centre leg (loss `β`), `lps` at `Pp` and at `{x}`, nonexpansion to stay below `rLeaf`. Constants `C' = CLeaf κ_P δ'`, `η = δ'/2` independent of `x`; `δ` depends on `x` through `κ_x`. |
| `bracket_construction_mem_shadowSet` | open: design | needs a plaque radius `r` with `plaque r p ⊆ Kplaque p` uniform over `p` near `x`; the field gives `r` per `p`. Middle and future constraints do follow from G4, G6 and the Bowen ball. |
| `bracket_approx_forward/backward`, `bracket_approx` | open: program (+design) | periodic search near the terminal datum, decoder call, rounding to `2^{-(Λ'+1)T}`; correctness needs the membership lemma. |
| `exists_lebesgue_innerBox` | proved | `lebesgue_number_lemma_of_metric` on `univ`, radius halved. |
| `Wloc_subset_closedBall_of_small` (S7) | proved | with `εx ≤ rLeaf`. |
| `net_approx` | open: program | cover `closure (innerBox j)` by enumerated periodic points, keep those certified within `r` (dovetailed `< r` / `> 3r/4` tests), run both bracket programs. |

---

## 7. Chapters F–I

### 7.1 F — `Geodesic/PlaqueNeighborhoods.lean`
Proved: `exists_cover_hypotheses` (G7, G8, G3 near a compact regular set, all scales below one
threshold), `perturbed_cover`, `perturbed_cover_scaled` (`C₂ = Cκ + 2C₁`), `abs_birkhoff_uPlus/uMinus_sub_le`
(`ω_p ≤ ρ/4` at the data radius), `ballUnion` (now a function of the presentation, not a method),
`ballUnion_ceOpen`. Open at the snapshot (worker active): `exact_cover_cs/cu` (pure set
arithmetic), `exists_computable_scalePlus/Minus` (rational rounding of the quadrature),
`effective_neighborhoods` (program), `proj_mem_plaques` (needs a bound on `dW .cs x (φ t x)` by the
flow displacement; no field gives one — candidate field G3'': `dW .cs x (φ s x) ≤ V |s|` for
`|s| ≤ 1`, and symmetric for `cu`).

### 7.2 G — `Geodesic/SectionReconstruction.lean`
Proved: `dist_le_of_mem_thickenings`, `diam_tubes_le`, `transverse_estimate_mono`,
`exists_basicBall_code`, `isREIn_secPt_mem`, `section_localization`, `exists_secPt_mem`,
`max_scale_eq`. Open: `section_reconstruction` (program: search `secPt j` for the first point
certified in `U^{cs} ∩ U^{cu} ∩ basicBall (c, rV)`, round to `max(Rp, Rm)`; `C₃ = Ltr C₂ + 1`).

### 7.3 H — `Geodesic/OrbitToLocation.lean` — sorry-free
`combinedScale` and its identities; `precisionComplexityNat_anti`, `_le_of_dist_lt`;
`oraclePairComplexity_le_log` (`2log₂(Tp+1) + 2log₂(Tm+1) + c`) and `_sublinear`;
`oracleNatComplexity_le_of_decoder` (three-input composition through `natBits`/`pairCode`);
`partrecIn_mono`; **`orbit_to_location`**, `_log`, `_regU`, `combinedScale_le_of_tendsto`,
`orbit_to_location_lyapunov`. These are proved from `section_reconstruction` as a black box, so
their validity is conditional on closing that one program.

### 7.4 I — `Geodesic/UpperBound.lean`
Proved: `ControlledReturns`, `.mem_Reg`, `controlledReturns_of_real` (real-time definition ⇒
integer-time one, endpoint sets enlarged by `φ([-1,0])`), `PositiveRates.exists_linear`,
`birkhoff_uPlus/uMinus_bounds`, `exists_stopping_times`, `return_adjustment` (constants
`θ = 2ρ(c−1)/λ̲`, `θ' = 2(ρ + Λ'(c−1))/λ̲`, `κ₀`, `κ₁` as in v1), `limsup_comp_le_of_tendsto_atTop`,
`liminf_nhdsWithin_le_liminf_seq`, **`sectionPoint_upper`**, `flow_coordinate_proj`,
**`main_pointwise`**, **`main_set`**, `bsPointToSet_cone_forward/backward`.
Open at the snapshot (worker active): `precision_chain` (assembly with explicit scale sequence),
`sectionPoint_mixed` (needs `orbit_extension_normalized`, now with rational radius),
`flow_coordinate` (computability of `φ q (ι i)` for rational `q`; `flow_coordinate_proj` is proved
from it), `orbitToLocationEstimate_of_smallPlaques` (Section 8.1).

Statement shapes as formalized:

```
main_pointwise : charOracle B ≤ᵀ charOracle A → OrbitToLocationEstimate G P A →
  ControlledReturns G x → PositiveRates G x →
  Dim^A(x) ≤ 1 + Dim^A_BS(x, f, u⁺) + Dim^A_BS(x, f⁻¹, u⁻) ∧
  dim^A(x) ≤ 1 + min (dim^A_BS(x,f,u⁺) + Dim^A_BS(x,f⁻¹,u⁻)) (Dim^A_BS(x,f,u⁺) + dim^A_BS(x,f⁻¹,u⁻))

main_set : (∀ A, B ≤ᵀ A → OrbitToLocationEstimate G P A) → (∀ x ∈ Z, ControlledReturns G x) →
  (∀ x ∈ Z, PositiveRates G x) →
  metricPackingDimension Z ≤ 1 + Dim_BS(Z,f,u⁺) + Dim_BS(Z,f⁻¹,u⁻) ∧
  dimH Z ≤ 1 + min (dim_BS(Z,f,u⁺) + Dim_BS(Z,f⁻¹,u⁻)) (Dim_BS(Z,f,u⁺) + dim_BS(Z,f⁻¹,u⁻))
```

---

## 8. What remains, and the fix for each

### 8.1 Design: shrinkable plaques (blocks E's correctness and the I ↔ H link)
Replace the fixed `Kplaque, Kplaque' : X → Set X` (G10) and their effective versions in Chapter C by
radius-indexed families `Kplaque : ℚ → X → Set X` with
`plaque .u (r/2) p ⊆ Kplaque r p ⊆ closure (plaque .u r p)`, computably compact uniformly in
`(k, r)`. Then: the decoders take `r` as input; `SmallPlaques Q ε₀` becomes a choice of `r ≤ ε₀`;
`bracket_construction_mem_shadowSet` holds with `r` chosen below the uniform `ε₀` of
`plaque_expansivity`; `orbitToLocationEstimate_of_smallPlaques` loses its hypothesis and becomes
`orbitToLocationEstimate_of_base`. Touches B (two fields), C (two fields), D–E (an extra argument).

### 8.2 Library: one certified-search lemma (blocks D's four decoders, hence E–G programs)
Shape: for a primcodable input type `ι` and candidate type `ℕ`, if the relation
`Cert : ι × ℕ → Prop` is `A`-c.e. and for every valid input some candidate is certified, then the
function returning the first certified candidate (dovetailing stage and candidate) is
`A`-partial recursive, halts on valid inputs, and returns a certified candidate. Buildable from
`relative_closure_rfind`/`rfindOpt` and `relative_enumeration`. With it, `localization_decoder` is:
certificate = "`Kplaque ⊆ violationSet ∪ ball(c, 2⁻ᵖ)`" (semidecidable by
`IsComputablyCompactIn.subset_ceOpen_isREIn` and `shadowSet_compl_ceOpen`), termination by
`exists_subset_ball_of_iInter_eq_singleton`, correctness by `shadowSet_subsingleton`.

### 8.3 Library: small closure lemmas (block A's two)
A public computable-real-family lemma for `dist (T^[t] (ι i)) (ι m)`; an `IsREIn` closure lemma
for bounded `∀` over a `List`; a tuple-decompressor complexity bound with a list input.

### 8.4 Fields possibly still missing
`proj_mem_plaques` wants a flow-displacement bound on centre leaves (candidate G3'' above).
Decide after the F worker reports.

### 8.5 Remaining analytic items
`precision_chain`, `sectionPoint_mixed`, `flow_coordinate` (Chapter I), `exists_computable_scale*`
(Chapter F), `uPlus_represented` (Chapter C, quadrature): mechanical but long; no obstruction known.

### 8.6 Existence of the base oracle
`exists_effectiveGeodesicData`: coding countable data into an oracle; a conditional version exists.

---

## 9. Status appendix (generated; regenerate with `docs/geodesic/sorry_notes/inventory.py`)

Snapshot 2026-11-03, after wave 2 and the computability reorganization (steps 0–7 of
`docs/geodesic/computability_reorg_blueprint.md`, log in `docs/geodesic/sorry_notes/REORG_LOG.md`):
233 declarations in the Geodesic modules, **0 containing `sorry`**; `lake build KolmogorovMathlib`
green with 0 warnings; `scripts/audit.sh` OK; `main_pointwise`, `main_set` and
`orbitToLocationEstimate_of_base` depend only on `propext`, `Classical.choice`, `Quot.sound`.

| module | declarations | open | open names |
|---|---|---|---|
| FlowInterface | 46 | 0 |  |
| FlowInterface/OrbitExtension | 5 | 0 |  |
| GeometricData | 42 | 0 |  |
| EffectiveData | 21 | 0 |  |
| OrbitData | 26 | 0 |  |
| Localization | 24 | 0 |  |
| BracketApprox/Geometry | 10 | 0 |  |
| BracketApprox | 6 | 0 |  |
| PlaqueNeighborhoods | 6 | 0 |  |
| SectionReconstruction | 8 | 0 |  |
| OrbitToLocation | 9 | 0 |  |
| UpperBound/Returns | 14 | 0 |  |
| UpperBound/PrecisionChain | 9 | 0 |  |
| UpperBound/SectionPoint | 2 | 0 |  |
| UpperBound/Mixed | 1 | 0 |  |
| UpperBound | 4 | 0 |  |

Module layout after the reorganization: Layer 0 `Oracle/{Closure,Search,PrefixComplexity/NatBounds,
PrefixComplexity/Decoders,Encoding/Numerals}.lean`; Layer 1
`PointToSet/ComputableMetric/{Points,CeOpen,Compact,Represented}.lean`; Layer 2
`PointToSet/EffectiveLocalization/{Search,Charging}.lean`; Layer 3 the Geodesic modules above
(`UpperBound` split into `Returns`, `PrecisionChain`, `SectionPoint`, `Mixed` and the main file;
`BracketApprox/Geometry`, `FlowInterface/OrbitExtension`, new `OrbitData`).

The two quadrature items `uPlus_represented`, `uMinus_represented` (item 8.4 of Section 8) were
closed in reorganization step 6 **by assumption**: `EffectiveGeodesicData` now has fields
`admissible_f : IsAdmissible P G.f ![u⁺] B` and `admissible_finv : IsAdmissible P G.finv ![u⁻] B`;
the derivation from `lamU_represented` alone (effective quadrature) remains optional (NOTES_C.md).
The remaining non-mathematical debt: `mixed_core` (UpperBound/Mixed.lean) needs
`maxHeartbeats 1600000` (allow-listed); its 640-line proof should be split.

---

## 10. Wave-2 decisions (made after the first serial build; code in progress)

* **S9 — radius-indexed plaques (item 8.1, done in B).** `Kplaque, Kplaque' : ℚ → X → Set X` with
  `plaque (r/2) p ⊆ Kplaque r p ⊆ closure (plaque r p)` (`Kplaque_spec`, `Kplaque'_spec`). The
  effective fields become families over `(k, r)`, the decoders take `r` as an input, and
  `SmallPlaques Q ε₀` is redefined so that it is a theorem (`smallPlaques`), which makes every
  downstream `SmallPlaques` hypothesis dischargeable. Unblocks `bracket_construction_mem_shadowSet`
  and the bracket programs.
* **S10 — shifted sections (item 8.1b, done in B).** G11 is stated for `φ s '' D_j` with the section
  point `z = φ s (proj (φ (-s) x)) = φ t₀ x`, `t₀ = τ (φ (-s) x)`; the unshifted form is the theorem
  `transverse_estimate_zero`. The localization data carry a rational `s`, chosen after the loss
  parameter so that `|t₀| < ε_x` (continuity of `τ`, `τ (proj x) = 0`).
* **S11 — interface quantifies the section point per parameter.** Because `s` depends on
  `(Pp, Pm, ρ)`, `OrbitToLocationEstimate G P A` now reads: for every regular `x`, every pair of
  compact regular endpoint sets and every rational loss, there is `t₀` with `|t₀| ≤ aMax` and
  constants `ε, C, c₀` such that the orbit-to-location inequality holds at `φ t₀ x`. Chapter I
  applies the flow-coordinate inequality `Dim x ≤ 1 + Dim (φ t₀ x)` inside the parameter loop and
  only then takes the limits in `q, ρ, c`; `sectionPoint_upper/mixed` become statements about `x`
  with the `1 +` already present. This also removes the quantifier-order obstruction found by the
  Chapter I worker (box fixed per point versus per parameter).
* **S12 — statement repairs found during filling:** `precision_chain` needs `2ρ(c−1) < λ̲` (else
  `δ p → 0` fails); `exists_stopping_times` is provable only with `N₀ := 0` and a shrunk slope
  (the exported `lam, N₀` are all downstream uses); `exact_cover_*` need `1 ≤ κ, 1 ≤ C`;
  `IsCeOpenFamilyIn.inter` needs a computable metric table; `FlowBox.D_nonempty`.
* **S13 — `sectionPoint_mixed` route.** Not the blueprint's `n_k → c·n_k` padding (its cost depends
  on `c` through `ε(P^±(c))`); instead a forward return in `[n_k/c, n_k + c]`, padding by the
  constant `⌈c⌉₊` steps with the pointwise `orbit_extension`, loss `Λ'(c−1) n_k` absorbed in
  `ϑ = 2(ρ+Λ')(c−1)/λ̲`, liminf-realizing sequence from `Filter.exists_seq_tendsto_liminf`.
* **Library lemma still needed (Chapter A, in progress):**
  `K^A(n) ≤ log₂(n+1) + 2 log₂(log₂(n+1)+1) + c` via `oracle_coding_finite_mass`; the library's
  `2 log₂(n+1)` bound only gives `Dim x ≤ 2 + Dim z` in `flow_coordinate`.
