# Notes on Chapter E (`Geodesic/BracketApprox.lean`)

Status (wave 2, final): zero errors, **no `sorry`** (after the `Px` fix below; the earlier gap
lemmas `shadowSet_subsingleton_near`/`…Backward…` were removed). Proved: `bracket_construction_mem_shadowSet` (restated, radius explicit),
`bracket_approx_forward`, `bracket_approx_backward`, `bracket_approx`, `net_approx` (fully proved,
no isolated sorry needed), plus `smallPlaques`.

## The gap: `shadowSet_subsingleton_near` (and its backward mirror)
- Needed by `bracket_approx_forward` as stated: the program `brS` and the constants `ε, C₁` are
  chosen before `x`, and `x` ranges over all of `G.Reg`. The decoder's correctness requires the
  constraint set `shadowSet ρ' r kp i T kq` (base point `p = pIdx kp` within `δ` of `x`) to be a
  subsingleton for the fixed decoder tolerance `ρ'` and radius `r`.
- What Chapter B gives: `plaque_expansivity Q` ⇒ `shadowSet_subsingleton` with constants `a, ε₀`
  depending on a compact regular set `Q` **containing the base point `p`**. For `x` (hence `p`)
  arbitrary in `Reg`, no uniform `a` exists in general (expansivity degenerates near `Sing`), and
  uniqueness cannot be transported to the endpoint set `Pp` because no field bounds forward
  unstable expansion (the leaf distance of two shadow-set points at time `T` is uncontrolled).
- Stated with `sorry`, isolated: `shadowSet_subsingleton_near {Pp} (hPp) (hPpR) :
  ∃ a > 0, ∃ ε₀ > 0, ∀ x ∈ Reg, ∃ δ > 0, ∀ ρ ≥ 0, 2Lρ < a → ∀ kp, dist (pIdx kp) x < δ →
  ∀ r, 0 < r → r ≤ ε₀ → ∀ i T kq, φ T x ∈ Pp → (shadowSet ρ r kp i T kq).Subsingleton`.
- The **true** version is proved as `shadowSet_subsingleton_of_mem {Q} (hQ) (hQR)`: constants
  `a, ε₀, δ` from the closed thickening of `Q`, valid for `x ∈ Q`.
- Proposed statement fix for `bracket_approx_forward/backward`, `bracket_approx`, `net_approx`
  (and downstream `effective_neighborhoods`): restrict the base point to a compact regular set,
  e.g. `∀ x ∈ Pp` (resp. `x ∈ Pm`, `x ∈ Pp ∩ Pm`), or add a base set `Px` (compact, regular,
  `Px ⊆ interior Q`) with `∀ x ∈ Px`. Then the gap lemmas follow from
  `shadowSet_subsingleton_of_mem` in one line and the whole chapter is sorry-free.

## Statement changes (as instructed)
- `SmallPlaques Q ε₀ := ∀ p ∈ periodic ∩ Q, ∀ r : ℚ, 0 < r → r ≤ ε₀ → Kplaque r p ⊆ closure … ∧
  Kplaque' r p ⊆ closure …`, proved for all `Q, ε₀` by `smallPlaques`.
- `bracket_construction_mem_shadowSet` takes `(ε₀) (hε₀)` and concludes
  `∃ ε η r, 0 < r ∧ r ≤ ε₀ ∧ … ∈ E.shadowSet ρ' r kp i T kq`.

## New lemmas (all proved)
`two_zpow_neg_le_scaleMinus`, `dyadicRadius_eq_rpow`, `exists_nat_dyadicRadius_le_scalePlus/Minus`
(computable precision `N·T` with a hard-wired `N ≥ Λ/log 2 + 1`), `bowenBall_mono_radius`,
`exists_compact_nhds_regular`, `scaleMinus_eq_exp`, `accumulatedRateBackward_close_of_cu_leg`
(mirror of B's `accumulatedRate_close_of_cs_leg`, from `lamS_flow_close_of_cu_leg`),
`bracket_construction_mem_shadowSetBackward`, `bracket_construction_error_backward`,
`shadowSet_subsingleton_of_mem`.

## Programs
- `brS (kp, i, T) := (search kq with certificate dist (pIdx kq) (φ T (ι i)) < η₀).bind
  (loc (kp, r, i, T, kq, N·T))` with `loc` from `decoder_of_compl_ceOpen`; `C₁ = C' + 1`.
- `net (j, ip, im, Tp, Tm, r, h) := (search a stage t with certificate
  closure (innerBox j) ⊆ ⋃_{kp ∈ L((ip,r),t)} ball (pIdx kp) h ∪ {w | 3r/4 < dist w (ι ip)}).bind
  (run brS, brU along L((ip,r),t))`, where `L` is the prefix enumeration
  (`IsREIn.exists_prefixList`) of `{kp | dist (pIdx kp) (ι ip) < 15r/8}` and the list run is
  `PartrecIn.exists_list_mapM`. Kept points are within `15r/8 + r/8 = 2r` of `x`.


## Final statements after the `Px` fix (wave 2, uniqueness gap closed)

Each theorem takes an explicit compact regular **base set** `{Px : Set X} (hPx : IsCompact Px)
(hPxR : Px ⊆ G.Reg)` right after the endpoint sets, and quantifies `∀ x ∈ Px`; the constants may
depend on `Px`. The gap lemmas are gone: uniqueness comes from `shadowSet_subsingleton_of_mem` /
`shadowSetBackward_subsingleton_of_mem` (both proved). E and F are sorry-free.
Downstream: `section_reconstruction` should take `Px` too; `orbit_to_location` can instantiate
`Px := {x}` with `isCompact_singleton` and `Set.singleton_subset_iff.mpr hx`.

```lean
theorem bracket_approx_forward {Pp : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    {Px : Set X} (hPx : IsCompact Px) (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ brS : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} brS ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (T : ℝ) x ∈ Pp →
              ∀ i, P.ι i ∈ bowenBall G.f (T + 1) x ε →
                (brS (kp, i, T)).Dom ∧
                  ∀ q ∈ brS (kp, i, T),
                    dist (P.ι q) (G.bracketS (E.pIdx kp) x) ≤ C₁ * G.scalePlus ρ T x)
```

```lean
theorem bracket_approx_backward {Pm : Set X} (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg)
    {Px : Set X} (hPx : IsCompact Px) (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ brU : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} brU ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (-(T : ℝ)) x ∈ Pm →
              ∀ i, P.ι i ∈ bowenBall G.finv (T + 1) x ε →
                (brU (kp, i, T)).Dom ∧
                  ∀ q ∈ brU (kp, i, T),
                    dist (P.ι q) (G.bracketU x (E.pIdx kp)) ≤ C₁ * G.scaleMinus ρ T x)
```

```lean
theorem bracket_approx {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {Px : Set X} (hPx : IsCompact Px)
    (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ brS brU : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} brS ∧ PartrecIn {charOracle B} brU ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ kp, dist (E.pIdx kp) x < δ →
              (∀ T : ℕ, G.φ (T : ℝ) x ∈ Pp → ∀ i, P.ι i ∈ bowenBall G.f (T + 1) x ε →
                (brS (kp, i, T)).Dom ∧ ∀ q ∈ brS (kp, i, T),
                  dist (P.ι q) (G.bracketS (E.pIdx kp) x) ≤ C₁ * G.scalePlus ρ T x) ∧
              (∀ T : ℕ, G.φ (-(T : ℝ)) x ∈ Pm → ∀ i, P.ι i ∈ bowenBall G.finv (T + 1) x ε →
                (brU (kp, i, T)).Dom ∧ ∀ q ∈ brU (kp, i, T),
                  dist (P.ι q) (G.bracketU x (E.pIdx kp)) ≤ C₁ * G.scaleMinus ρ T x))
```

```lean
theorem net_approx {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {Px : Set X} (hPx : IsCompact Px)
    (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ net : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ →. List (ℕ × ℕ × ℕ),
        PartrecIn {charOracle B} net ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ (j : Fin G.nBoxes) (r h : ℚ), 0 < r → 2 * (r : ℝ) < δ →
              Metric.closedBall x (2 * r) ⊆ G.innerBox j → 0 < h → h ≤ r / 8 →
              ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
              ∀ ip im : ℕ, P.ι ip ∈ bowenBall G.f (Tp + 1) x (min ε (r / 8)) →
                P.ι im ∈ bowenBall G.finv (Tm + 1) x (min ε (r / 8)) →
                (net (j, ip, im, Tp, Tm, r, h)).Dom ∧
                  ∀ out ∈ net (j, ip, im, Tp, Tm, r, h),
                    (∀ e ∈ out, dist (E.pIdx e.1) x < 2 * r) ∧
                    Metric.closedBall x (r / 2) ⊆ ⋃ e ∈ out, Metric.ball (E.pIdx e.1) (h : ℝ) ∧
                    ∀ e ∈ out,
                      dist (P.ι e.2.1) (G.bracketS (E.pIdx e.1) x) ≤ C₁ * G.scalePlus ρ Tp x ∧
                      dist (P.ι e.2.2) (G.bracketU x (E.pIdx e.1)) ≤
                        C₁ * G.scaleMinus ρ Tm x)
```

```lean
theorem effective_neighborhoods {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {Px : Set X} (hPx : IsCompact Px)
    (hPxR : Px ⊆ G.Reg) (ρ : ℚ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ nbhd : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ →. List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ,
        PartrecIn {charOracle B} nbhd ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ (j : Fin G.nBoxes) (r : ℚ) (εx : ℝ), x ∈ (G.box j).U ∧ 0 < r ∧ 0 < εx ∧
            ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
            ∀ ip im : ℕ, P.ι ip ∈ bowenBall G.f (Tp + 1) x (min ε (r / 8)) →
              P.ι im ∈ bowenBall G.finv (Tm + 1) x (min ε (r / 8)) →
              (nbhd (j, ip, im, Tp, Tm, r)).Dom ∧
                ∀ out ∈ nbhd (j, ip, im, Tp, Tm, r),
                  G.plaque .cs εx x ⊆ ballUnion P out.1 ∧
                  ballUnion P out.1 ⊆ Metric.thickening (C₂ * G.scalePlus ρ Tp x) (G.Wloc .cs x) ∧
                  G.plaque .cu εx x ⊆ ballUnion P out.2.1 ∧
                  ballUnion P out.2.1 ⊆
                    Metric.thickening (C₂ * G.scaleMinus ρ Tm x) (G.Wloc .cu x) ∧
                  0 < out.2.2.1 ∧ G.scalePlus (ρ / 2) Tp x ≤ out.2.2.1 ∧
                    (out.2.2.1 : ℝ) ≤ G.scalePlus ρ Tp x ∧
                  0 < out.2.2.2 ∧ G.scaleMinus (ρ / 2) Tm x ≤ out.2.2.2 ∧
                    (out.2.2.2 : ℝ) ≤ G.scaleMinus ρ Tm x)
```
