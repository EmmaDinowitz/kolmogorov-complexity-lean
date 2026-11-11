/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.BracketApprox

/-!
# Plaque neighborhoods at integral scales (geodesic blueprint, Chapter F)

The nodes `geo:exact-cover` (OTL `lem:exact_plaque_cover`),
`geo:perturbed-cover` (OTL `cor:perturbed_plaque_cover`) and `geo:effective-neighborhoods`
(OTL `cor:radius_of_approximation`) of `geodesic_upper_bound_blueprint.md`.

The two covering lemmas are pure metric geometry about brackets with leg bounds and branch
consistency; they are stated with those bounds as explicit hypotheses, and a separate lemma
supplies the hypotheses near a compact regular set from the fields G7, G8 and G3.
Neighborhoods of a set `S` are `Metric.thickening r S = {y | infDist y S < r}`.

The effective statement produces, from forward and backward orbit data, two finite lists of
basic balls whose unions `U^{cs}`, `U^{cu}` contain the target plaques `W^{cs}_{ε_x}(x)`,
`W^{cu}_{ε_x}(x)` and lie in the `C₂ E_±(ρ)`-thickenings of the local plaques, together with
computable scales `R₊, R₋` with `E_±(ρ/2) ≤ R_± ≤ E_±(ρ)`. The scales come from effective
quadrature of `u^±` along the ideal orbit data (`OrbitDatum.scalePlus`, `OrbitDatum.scaleMinus`
in `OrbitData.lean`, built on `birkhoff_uPlus_computable` of Chapter C and the oscillation
bound `small_scale_oscillation_birkhoff` of the library); no exact integral along `x` is an
input. The loss `ρ` is rational so that the program can form `R_±`. The orbit data are
`OrbitDatum`s of orders `Tp + 1`, `Tm + 1` and tolerance at most `min ε (r / 8)`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-! ### `geo:exact-cover`: covering by exact bracket centers -/

/-- Covering a center stable plaque by balls about exact bracket centers (OTL
`lem:exact_plaque_cover`). If the points of `L` cover the plaque `W^{cs}_ε(x)` at mesh `h`,
brackets `[p,w]_s` have center stable legs bounded by `κ d(p,w)`, are branch consistent
(`[p,w]_s = [p,x]_s` for `w` in the plaque), lie in the local plaque, and leaf distance
dominates ambient distance by `C` on those legs, then
`W^{cs}_ε(x) ⊆ ⋃_{p ∈ L} B(C κ h, [p,x]_s) ⊆ thickening (C κ h) (W^{cs}_loc(x))`.
Blueprint node `geo:exact-cover`. -/
theorem exact_cover_cs (x : X) {ε κ C h : ℝ} (hκ : 1 ≤ κ) (hC : 1 ≤ C) (_hh : 0 < h) (L : List X)
    (hcover : ∀ w ∈ G.plaque .cs ε x, ∃ p ∈ L, dist p w < h)
    (hleg : ∀ p ∈ L, ∀ w ∈ G.plaque .cs ε x, dist p w < h →
      G.bracketS p w ∈ G.W .cs w ∧ G.dW .cs w (G.bracketS p w) ≤ κ * dist p w)
    (hbranch : ∀ p ∈ L, ∀ w ∈ G.plaque .cs ε x, dist p w < h → G.bracketS p w = G.bracketS p x)
    (hcenters : ∀ p ∈ L, G.bracketS p x ∈ G.Wloc .cs x)
    (hcomp : ∀ p ∈ L, ∀ w ∈ G.plaque .cs ε x, dist p w < h →
      dist (G.bracketS p w) w ≤ C * G.dW .cs w (G.bracketS p w)) :
    G.plaque .cs ε x ⊆ ⋃ p ∈ L, Metric.ball (G.bracketS p x) (C * κ * h) ∧
      (⋃ p ∈ L, Metric.ball (G.bracketS p x) (C * κ * h)) ⊆
        Metric.thickening (C * κ * h) (G.Wloc .cs x) := by
  have hCκ : 0 < C * κ := by positivity
  refine ⟨fun w hw ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨p, hp, hpw⟩ := hcover w hw
    obtain ⟨-, hleg'⟩ := hleg p hp w hw hpw
    have hc := hcomp p hp w hw hpw
    rw [Set.mem_iUnion₂]
    refine ⟨p, hp, ?_⟩
    rw [Metric.mem_ball, dist_comm, ← hbranch p hp w hw hpw]
    calc dist (G.bracketS p w) w ≤ C * G.dW .cs w (G.bracketS p w) := hc
      _ ≤ C * (κ * dist p w) := mul_le_mul_of_nonneg_left hleg' (by linarith)
      _ < C * κ * h := by rw [← mul_assoc]; exact mul_lt_mul_of_pos_left hpw hCκ
  · rw [Set.mem_iUnion₂] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [Metric.mem_thickening_iff]
    exact ⟨G.bracketS p x, hcenters p hp, hy⟩

/-- Center unstable counterpart, with `[w,p]_u = [x,p]_u` for `w ∈ W^{cu}_ε(x)`.
Blueprint node `geo:exact-cover`. -/
theorem exact_cover_cu (x : X) {ε κ C h : ℝ} (hκ : 1 ≤ κ) (hC : 1 ≤ C) (_hh : 0 < h) (L : List X)
    (hcover : ∀ w ∈ G.plaque .cu ε x, ∃ p ∈ L, dist p w < h)
    (hleg : ∀ p ∈ L, ∀ w ∈ G.plaque .cu ε x, dist p w < h →
      G.bracketU w p ∈ G.W .cu w ∧ G.dW .cu w (G.bracketU w p) ≤ κ * dist p w)
    (hbranch : ∀ p ∈ L, ∀ w ∈ G.plaque .cu ε x, dist p w < h → G.bracketU w p = G.bracketU x p)
    (hcenters : ∀ p ∈ L, G.bracketU x p ∈ G.Wloc .cu x)
    (hcomp : ∀ p ∈ L, ∀ w ∈ G.plaque .cu ε x, dist p w < h →
      dist (G.bracketU w p) w ≤ C * G.dW .cu w (G.bracketU w p)) :
    G.plaque .cu ε x ⊆ ⋃ p ∈ L, Metric.ball (G.bracketU x p) (C * κ * h) ∧
      (⋃ p ∈ L, Metric.ball (G.bracketU x p) (C * κ * h)) ⊆
        Metric.thickening (C * κ * h) (G.Wloc .cu x) := by
  have hCκ : 0 < C * κ := by positivity
  refine ⟨fun w hw ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨p, hp, hpw⟩ := hcover w hw
    obtain ⟨-, hleg'⟩ := hleg p hp w hw hpw
    have hc := hcomp p hp w hw hpw
    rw [Set.mem_iUnion₂]
    refine ⟨p, hp, ?_⟩
    rw [Metric.mem_ball, dist_comm, ← hbranch p hp w hw hpw]
    calc dist (G.bracketU w p) w ≤ C * G.dW .cu w (G.bracketU w p) := hc
      _ ≤ C * (κ * dist p w) := mul_le_mul_of_nonneg_left hleg' (by linarith)
      _ < C * κ * h := by rw [← mul_assoc]; exact mul_lt_mul_of_pos_left hpw hCκ
  · rw [Set.mem_iUnion₂] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [Metric.mem_thickening_iff]
    exact ⟨G.bracketU x p, hcenters p hp, hy⟩

/-- Near a compact regular set the hypotheses of the covering lemmas hold with the local
product constants of G7, the branch consistency scale of G8 and the comparison constant
`CLeaf` of G3, for all plaque radii `ε` and meshes `h` below a threshold `δ`.
Blueprint nodes `geo:exact-cover`, `geo:lps-from-compact`. -/
theorem exists_cover_hypotheses {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ κ : ℝ, 1 ≤ κ ∧ ∀ x : X, (∃ q ∈ Q, dist x q < δ) →
      ∀ ε h : ℝ, 0 < ε → ε ≤ δ → 0 < h → h ≤ δ → ∀ p : X, dist p x < δ →
        (∀ w ∈ G.plaque .cs ε x, dist p w < h →
          (G.bracketS p w ∈ G.W .cs w ∧ G.dW .cs w (G.bracketS p w) ≤ κ * dist p w) ∧
          G.bracketS p w = G.bracketS p x ∧
          dist (G.bracketS p w) w ≤ G.CLeaf * G.dW .cs w (G.bracketS p w)) ∧
        G.bracketS p x ∈ G.Wloc .cs x ∧
        (∀ w ∈ G.plaque .cu ε x, dist p w < h →
          (G.bracketU w p ∈ G.W .cu w ∧ G.dW .cu w (G.bracketU w p) ≤ κ * dist p w) ∧
          G.bracketU w p = G.bracketU x p ∧
          dist (G.bracketU w p) w ≤ G.CLeaf * G.dW .cu w (G.bracketU w p)) ∧
        G.bracketU x p ∈ G.Wloc .cu x := by
  obtain ⟨δ₁, hδ₁, κ, hκ, hlps⟩ := G.lps Q hQ hQR
  obtain ⟨δ₂, hδ₂, hbc⟩ := G.branch_consistency Q hQ hQR
  have hκ0 : 0 < κ := lt_of_lt_of_le one_pos hκ
  have hr := G.rLeaf_pos
  set δ := min (min (δ₁ / 3) (δ₂ / 3)) (G.rLeaf / κ) with hδ
  have hδpos : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (div_pos hr hκ0)
  refine ⟨δ, hδpos, κ, hκ, ?_⟩
  intro x hx ε h hε hεδ hh hhδ p hpx
  have hδ1 : δ ≤ δ₁ / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ / 3 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ G.rLeaf / κ := min_le_right _ _
  have hκδ : κ * δ ≤ G.rLeaf := by rwa [le_div_iff₀ hκ0, mul_comm] at hδ3
  obtain ⟨q, hqQ, hxq⟩ := hx
  have hpQ : dist p q < 2 * δ := by
    calc dist p q ≤ dist p x + dist x q := dist_triangle _ _ _
      _ < δ + δ := add_lt_add hpx hxq
      _ = 2 * δ := by ring
  refine ⟨fun w hw hpw ↦ ?_, ?_, fun w hw hpw ↦ ?_, ?_⟩
  · have hw' : w ∈ G.W .cs x ∧ G.dW .cs x w < ε := hw
    obtain ⟨-, -, h1, h2, -⟩ := (hlps p w ⟨q, hqQ, by linarith⟩ (by linarith)).1
    have hdW : G.dW .cs w (G.bracketS p w) < G.rLeaf := by
      calc G.dW .cs w (G.bracketS p w) ≤ κ * dist p w := h2
        _ < κ * δ := by gcongr; linarith
        _ ≤ G.rLeaf := hκδ
    refine ⟨⟨h1, h2⟩, ?_, ?_⟩
    · exact (hbc p x w ⟨q, hqQ, by linarith⟩ (by linarith) (by linarith)).1 hw'.1
        (by linarith [hw'.2])
    · rw [dist_comm]
      exact G.dist_le_CLeaf_mul_dW .cs w _ h1 hdW
  · obtain ⟨-, -, h1, h2, -⟩ := (hlps p x ⟨q, hqQ, by linarith⟩ (by linarith)).1
    refine ⟨h1, lt_of_le_of_lt h2 ?_⟩
    calc κ * dist p x < κ * δ := by gcongr
      _ ≤ G.rLeaf := hκδ
  · have hw' : w ∈ G.W .cu x ∧ G.dW .cu x w < ε := hw
    have hwQ : ∃ q ∈ Q, dist w q < δ₁ := by
      refine ⟨q, hqQ, ?_⟩
      calc dist w q ≤ dist w p + dist p q := dist_triangle _ _ _
        _ < δ + 2 * δ := add_lt_add (by rw [dist_comm]; linarith) hpQ
        _ ≤ δ₁ := by linarith
    obtain ⟨h1, h2, -, -, -⟩ := (hlps w p hwQ (by rw [dist_comm]; linarith)).2
    rw [dist_comm] at h2
    have hdW : G.dW .cu w (G.bracketU w p) < G.rLeaf := by
      calc G.dW .cu w (G.bracketU w p) ≤ κ * dist p w := h2
        _ < κ * δ := by gcongr; linarith
        _ ≤ G.rLeaf := hκδ
    refine ⟨⟨h1, h2⟩, ?_, ?_⟩
    · exact (hbc p x w ⟨q, hqQ, by linarith⟩ (by linarith) (by linarith)).2 hw'.1
        (by linarith [hw'.2])
    · rw [dist_comm]
      exact G.dist_le_CLeaf_mul_dW .cu w _ h1 hdW
  · obtain ⟨h1, h2, -, -, -⟩ := (hlps x p ⟨q, hqQ, by linarith⟩ (by rw [dist_comm]; linarith)).2
    refine ⟨h1, lt_of_le_of_lt h2 ?_⟩
    calc κ * dist x p < κ * δ := by gcongr; rwa [dist_comm]
      _ ≤ G.rLeaf := hκδ

/-! ### `geo:perturbed-cover`: perturbed bracket centers -/

omit [CompactSpace X] in
/-- Perturbed centers (OTL `cor:perturbed_plaque_cover`): if the plaque is covered by balls of
radius `s` about centers `c p ∈ S` and `d(y p, c p) ≤ a`, then it is covered by balls of radius
`s + a` about the `y p`, and those balls lie in the `(s + 2a)`-thickening of `S`. The center
error is counted once for covering and once more for containment.
Blueprint node `geo:perturbed-cover`. -/
theorem perturbed_cover {ι : Type*} (L : List ι) (c y : ι → X) (S Z : Set X) {s a : ℝ}
    (_hs : 0 ≤ s) (_ha : 0 ≤ a) (hcover : Z ⊆ ⋃ p ∈ L, Metric.ball (c p) s)
    (hcenters : ∀ p ∈ L, c p ∈ S) (herr : ∀ p ∈ L, dist (y p) (c p) ≤ a) :
    Z ⊆ ⋃ p ∈ L, Metric.ball (y p) (s + a) ∧
      (⋃ p ∈ L, Metric.ball (y p) (s + a)) ⊆ Metric.thickening (s + 2 * a) S := by
  constructor
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp (hcover hz)
    refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    rw [Metric.mem_ball] at hzp ⊢
    calc dist z (y p) ≤ dist z (c p) + dist (c p) (y p) := dist_triangle _ _ _
      _ < s + a := by
        rw [dist_comm (c p)]
        exact add_lt_add_of_lt_of_le hzp (herr p hp)
  · intro w hw
    obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hw
    rw [Metric.mem_ball] at hwp
    refine Metric.mem_thickening_iff.mpr ⟨c p, hcenters p hp, ?_⟩
    calc dist w (c p) ≤ dist w (y p) + dist (y p) (c p) := dist_triangle _ _ _
      _ < s + a + a := add_lt_add_of_lt_of_le hwp (herr p hp)
      _ = s + 2 * a := by ring

omit [CompactSpace X] in
/-- With mesh `h ≤ R` and center error `a ≤ C₁ R`, the covering radius is `(C κ + C₁) R` and the
containment radius `(C κ + 2 C₁) R`: the constants `C₂ = C κ + 2 C₁` of the drafts.
Blueprint node `geo:perturbed-cover`. -/
theorem perturbed_cover_scaled {ι : Type*} (L : List ι) (c y : ι → X) (S Z : Set X)
    {C κ C₁ R h a : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ) (_hC₁ : 0 ≤ C₁) (_hR : 0 < R) (hh : h ≤ R)
    (_hh0 : 0 ≤ h) (ha : a ≤ C₁ * R) (_ha0 : 0 ≤ a)
    (hcover : Z ⊆ ⋃ p ∈ L, Metric.ball (c p) (C * κ * h))
    (hcenters : ∀ p ∈ L, c p ∈ S) (herr : ∀ p ∈ L, dist (y p) (c p) ≤ a) :
    Z ⊆ ⋃ p ∈ L, Metric.ball (y p) ((C * κ + C₁) * R) ∧
      (⋃ p ∈ L, Metric.ball (y p) ((C * κ + C₁) * R)) ⊆
        Metric.thickening ((C * κ + 2 * C₁) * R) S := by
  have h1 : C * κ * h ≤ C * κ * R := mul_le_mul_of_nonneg_left hh (mul_nonneg hC hκ)
  constructor
  · intro z hz
    obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp (hcover hz)
    refine Set.mem_iUnion₂.mpr ⟨p, hp, ?_⟩
    rw [Metric.mem_ball] at hzp ⊢
    calc dist z (y p) ≤ dist z (c p) + dist (c p) (y p) := dist_triangle _ _ _
      _ < C * κ * h + a := by
        rw [dist_comm (c p)]
        exact add_lt_add_of_lt_of_le hzp (herr p hp)
      _ ≤ (C * κ + C₁) * R := by linarith
  · intro w hw
    obtain ⟨p, hp, hwp⟩ := Set.mem_iUnion₂.mp hw
    rw [Metric.mem_ball] at hwp
    refine Metric.mem_thickening_iff.mpr ⟨c p, hcenters p hp, ?_⟩
    calc dist w (c p) ≤ dist w (y p) + dist (y p) (c p) := dist_triangle _ _ _
      _ < (C * κ + C₁) * R + a := add_lt_add_of_lt_of_le hwp (herr p hp)
      _ ≤ (C * κ + 2 * C₁) * R := by linarith

end GeodesicReconstructionData

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### `geo:effective-neighborhoods` -/

/-- Effective neighborhoods at integral scales (OTL `cor:radius_of_approximation`). For compact
regular endpoint sets and a rational loss `ρ` there are a tolerance `ε`, a constant `C₂`, a
plaque threshold `ε₀`, a compact neighborhood `Q` of the endpoint sets, and one `B`-partial
recursive program `nbhd` such that, when the compact plaques over `Q` are `ε₀`-small: every
regular `x` has a localization (a box `j`, a radius `r`, a target plaque radius `ε_x`) such that
for regular endpoints `φ Tp x ∈ Pp`, `φ (-Tm) x ∈ Pm` and orbit data `dp, dm` of orders
`Tp + 1`, `Tm + 1` at tolerance at most `min ε (r/8)`, the program halts on
`(j, dp.idx, dm.idx, Tp, Tm, r)` with two lists of basic balls and two positive rationals
`Rp, Rm` satisfying
`W^{cs}_{ε_x}(x) ⊆ U^{cs} ⊆ thickening (C₂ E₊(ρ)) (W^{cs}_loc(x))`,
`W^{cu}_{ε_x}(x) ⊆ U^{cu} ⊆ thickening (C₂ E₋(ρ)) (W^{cu}_loc(x))`,
`E₊(ρ/2) ≤ Rp ≤ E₊(ρ)`, `E₋(ρ/2) ≤ Rm ≤ E₋(ρ)`.
The program forms `Rp, Rm` by `OrbitDatum.scalePlus/scaleMinus`, picks a rational mesh
`h < min Rp Rm` (and `≤ r/8`), runs `net_approx` at loss `ρ/2`, and returns the balls of radius
`(CLeaf κ + C₁) Rp` about the forward outputs and `(CLeaf κ + C₁) Rm` about the backward
outputs; `perturbed_cover_scaled` gives `C₂ = CLeaf κ + 2 C₁`.
Blueprint node `geo:effective-neighborhoods`. -/
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
            ∀ (dp : OrbitDatum P G.f x) (dm : OrbitDatum P G.finv x),
              dp.order = Tp + 1 → dp.tol ≤ min ε (r / 8) →
              dm.order = Tm + 1 → dm.tol ≤ min ε (r / 8) →
              (nbhd (j, dp.idx, dm.idx, Tp, Tm, r)).Dom ∧
                ∀ out ∈ nbhd (j, dp.idx, dm.idx, Tp, Tm, r),
                  G.plaque .cs εx x ⊆ ballUnion P out.1 ∧
                  ballUnion P out.1 ⊆ Metric.thickening (C₂ * G.scalePlus ρ Tp x) (G.Wloc .cs x) ∧
                  G.plaque .cu εx x ⊆ ballUnion P out.2.1 ∧
                  ballUnion P out.2.1 ⊆
                    Metric.thickening (C₂ * G.scaleMinus ρ Tm x) (G.Wloc .cu x) ∧
                  0 < out.2.2.1 ∧ G.scalePlus (ρ / 2) Tp x ≤ out.2.2.1 ∧
                    (out.2.2.1 : ℝ) ≤ G.scalePlus ρ Tp x ∧
                  0 < out.2.2.2 ∧ G.scaleMinus (ρ / 2) Tm x ≤ out.2.2.2 ∧
                    (out.2.2.2 : ℝ) ≤ G.scaleMinus ρ Tm x) := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hmono : ∀ (T : X → X) (n : ℕ) (x : X) {ε ε' : ℝ}, ε ≤ ε' →
      bowenBall T n x ε ⊆ bowenBall T n x ε' := fun T n x ε ε' hle y hy ↦
    Dynamics.dynEntourage_monotone T n (fun z hz ↦ lt_of_lt_of_le hz hle) hy
  obtain ⟨ε₁, hε₁, C₁, hC₁, ε₀, hε₀, Q, hQ, hPQ, hQR, net, hnet, hspec⟩ :=
    E.net_approx hPp hPpR hPm hPmR hPx hPxR (ρ := (ρ : ℝ) / 2) (by positivity)
  obtain ⟨εp, hεp, Rp, hRp, hRpspec⟩ := OrbitDatum.scalePlus E ρ hρ
  obtain ⟨εm, hεm, Rm, hRm, hRmspec⟩ := OrbitDatum.scaleMinus E ρ hρ
  obtain ⟨c₁, hc₁⟩ := exists_rat_gt C₁
  have hc₁0 : (0 : ℝ) < c₁ := hC₁.trans hc₁
  obtain ⟨ℓ, hℓ, hleb⟩ := exists_lebesgue_innerBox (G := G)
  have hCLeaf : 0 < G.CLeaf := by linarith [G.one_le_CLeaf]
  -- rational minimum
  have hminq : Computable₂ fun a b : ℚ ↦ min a b := by
    have h : Computable fun p : ℚ × ℚ ↦ bif decide (p.2 < p.1) then p.2 else p.1 :=
      Computable.cond (computable₂_ratLt.comp Computable.snd Computable.fst) Computable.snd
        Computable.fst
    refine h.of_eq fun p ↦ ?_
    rcases lt_or_ge p.2 p.1 with h | h
    · simp [h, min_eq_right h.le]
    · simp [not_lt.mpr h, min_eq_left h]
  -- projections of the input
  have pip : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦ d.2.1 :=
    Computable.fst.comp Computable.snd
  have pim : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦ d.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have pTp : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦ d.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have pTm : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦ d.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      Computable.snd)))
  have pr : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦ d.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      Computable.snd)))
  have hRp' : ComputableIn {charOracle B} fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦
      Rp (d.2.1, d.2.2.2.1) :=
    hRp.comp (pip.pair pTp).computableIn
  have hRm' : ComputableIn {charOracle B} fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦
      Rm (d.2.2.1, d.2.2.2.2.1) :=
    hRm.comp (pim.pair pTm).computableIn
  -- the mesh
  obtain ⟨mesh, hmesh_def⟩ : ∃ mesh : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ → ℚ, mesh = fun d ↦
      min (min (Rp (d.2.1, d.2.2.2.1)) (Rm (d.2.2.1, d.2.2.2.2.1))) 1 * d.2.2.2.2.2 / 8 :=
    ⟨_, rfl⟩
  have hmesh : ComputableIn {charOracle B} mesh := by
    rw [hmesh_def]
    exact (computable_ratDivConst (by norm_num : (0 : ℚ) < 8)).computableIn.comp
      (computable₂_ratMul.computableIn₂.comp
        (hminq.computableIn₂.comp (hminq.computableIn₂.comp hRp' hRm') (ComputableIn.const 1))
        pr.computableIn)
  have hg : ComputableIn {charOracle B} fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦
      (d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2, mesh d) :=
    Computable.fst.computableIn.pair (pip.computableIn.pair (pim.computableIn.pair
      (pTp.computableIn.pair (pTm.computableIn.pair (pr.computableIn.pair hmesh)))))
  have hrun : PartrecIn {charOracle B} fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ ↦
      net (d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2, mesh d) :=
    hnet.comp hg
  -- the output transformation
  obtain ⟨post, hpost_def⟩ : ∃ post : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) →
      List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ, post = fun p ↦
        (p.2.map (fun e ↦ (e.2.1, (1 + c₁) * Rp (p.1.2.1, p.1.2.2.2.1))),
          p.2.map (fun e ↦ (e.2.2, (1 + c₁) * Rm (p.1.2.2.1, p.1.2.2.2.2.1))),
          Rp (p.1.2.1, p.1.2.2.2.1), Rm (p.1.2.2.1, p.1.2.2.2.2.1)) := ⟨_, rfl⟩
  have hpost : ComputableIn {charOracle B} post := by
    rw [hpost_def]
    have hRpp : ComputableIn {charOracle B}
        fun p : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) ↦
          Rp (p.1.2.1, p.1.2.2.2.1) :=
      (hRp'.comp ComputableIn.fst).of_eq fun _ ↦ rfl
    have hRmp : ComputableIn {charOracle B}
        fun p : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) ↦
          Rm (p.1.2.2.1, p.1.2.2.2.2.1) :=
      (hRm'.comp ComputableIn.fst).of_eq fun _ ↦ rfl
    have hradp : ComputableIn {charOracle B}
        fun p : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) ↦
          (1 + c₁) * Rp (p.1.2.1, p.1.2.2.2.1) :=
      computable₂_ratMul.computableIn₂.comp (ComputableIn.const _) hRpp
    have hradm : ComputableIn {charOracle B}
        fun p : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) ↦
          (1 + c₁) * Rm (p.1.2.2.1, p.1.2.2.2.2.1) :=
      computable₂_ratMul.computableIn₂.comp (ComputableIn.const _) hRmp
    have hm1 : Computable fun q : List (ℕ × ℕ × ℕ) × ℚ ↦ q.1.map (fun e ↦ (e.2.1, q.2)) :=
      Computable.list_map Computable.fst
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (Computable.snd.comp Computable.fst))
    have hm2 : Computable fun q : List (ℕ × ℕ × ℕ) × ℚ ↦ q.1.map (fun e ↦ (e.2.2, q.2)) :=
      Computable.list_map Computable.fst
        ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
          (Computable.snd.comp Computable.fst))
    have hL1 : ComputableIn {charOracle B}
        fun p : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) ↦
          p.2.map (fun e ↦ (e.2.1, (1 + c₁) * Rp (p.1.2.1, p.1.2.2.2.1))) :=
      (hm1.computableIn.comp (ComputableIn.snd.pair hradp)).of_eq fun _ ↦ rfl
    have hL2 : ComputableIn {charOracle B}
        fun p : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ) × List (ℕ × ℕ × ℕ) ↦
          p.2.map (fun e ↦ (e.2.2, (1 + c₁) * Rm (p.1.2.2.1, p.1.2.2.2.2.1))) :=
      (hm2.computableIn.comp (ComputableIn.snd.pair hradm)).of_eq fun _ ↦ rfl
    exact hL1.pair (hL2.pair (hRpp.pair hRmp))
  obtain ⟨nbhd, hnbhd_def⟩ : ∃ nbhd : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ →.
      List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ, nbhd = fun d ↦
        (net (d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1, d.2.2.2.2.2, mesh d)).map
          (fun out ↦ post (d, out)) := ⟨_, rfl⟩
  have hnbhd : PartrecIn {charOracle B} nbhd := by
    rw [hnbhd_def]
    exact hrun.map (ComputableIn₂.mk (f := fun d out ↦ post (d, out)) hpost)
  refine ⟨min ε₁ (min εp εm), by positivity, 1 + 2 * (c₁ : ℝ), by positivity, ε₀, hε₀, Q, hQ,
    hPQ, hQR, nbhd, hnbhd, fun hsmall x hx ↦ ?_⟩
  obtain ⟨δn, hδn, hnetx⟩ := hspec hsmall x hx
  obtain ⟨δc, hδc, κ, hκ, hcov⟩ :=
    G.exists_cover_hypotheses (Q := {x}) isCompact_singleton
      (Set.singleton_subset_iff.mpr (hPxR hx))
  obtain ⟨j, hj⟩ := hleb x
  have hκ0 : 0 < κ := by linarith
  have hxQ : ∃ q ∈ ({x} : Set X), dist x q < δc := ⟨x, rfl, by simpa using hδc⟩
  -- the radius
  have hm0 : 0 < min (min (ℓ / 2) (δn / 4)) (min (δc / 4) (8 / (G.CLeaf * κ))) := by positivity
  obtain ⟨r, hr0, hrm⟩ := exists_rat_btwn hm0
  have hr0' : (0 : ℚ) < r := by exact_mod_cast hr0
  have hr1 : 2 * (r : ℝ) ≤ ℓ := by
    have := hrm.trans_le ((min_le_left _ _).trans (min_le_left _ _)); linarith
  have hr2 : 2 * (r : ℝ) < δn := by
    have := hrm.trans_le ((min_le_left _ _).trans (min_le_right _ _)); linarith
  have hr3 : 2 * (r : ℝ) ≤ δc := by
    have := hrm.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hr4 : G.CLeaf * κ * r / 8 ≤ 1 := by
    have := hrm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  -- the plaque radius
  have hεx0 : 0 < min (min ((r : ℝ) / (2 * G.CLeaf)) G.rLeaf) δc := by
    have := G.rLeaf_pos; positivity
  have hxU : x ∈ (G.box j).U :=
    G.closure_innerBox_subset j (subset_closure (hj (Metric.mem_closedBall_self hℓ.le)))
  refine ⟨j, r, min (min ((r : ℝ) / (2 * G.CLeaf)) G.rLeaf) δc, hxU, hr0', hεx0,
    fun Tp Tm hTp hTm dp dm hdpT hdptol hdmT hdmtol ↦ ?_⟩
  have hip := dp.mem_order hdpT hdptol
  have him := dm.mem_order hdmT hdmtol
  generalize dp.idx = ip at hip ⊢
  generalize dm.idx = im at him ⊢
  generalize hεx : min (min ((r : ℝ) / (2 * G.CLeaf)) G.rLeaf) δc = εx at hεx0
  have hεxr : εx ≤ G.rLeaf := by rw [← hεx]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hεxδ : εx ≤ δc := by rw [← hεx]; exact min_le_right _ _
  have hCεx : G.CLeaf * εx ≤ r / 2 := by
    have : εx ≤ (r : ℝ) / (2 * G.CLeaf) := by
      rw [← hεx]; exact (min_le_left _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hball : Metric.closedBall x (2 * r) ⊆ G.innerBox j :=
    (Metric.closedBall_subset_closedBall hr1).trans hj
  have hip1 : P.ι ip ∈ bowenBall G.f (Tp + 1) x (min ε₁ (r / 8)) :=
    hmono _ _ _ (min_le_min (min_le_left _ _) le_rfl) hip
  have him1 : P.ι im ∈ bowenBall G.finv (Tm + 1) x (min ε₁ (r / 8)) :=
    hmono _ _ _ (min_le_min (min_le_left _ _) le_rfl) him
  have hipp : P.ι ip ∈ bowenBall G.f (Tp + 1) x εp :=
    hmono _ _ _ ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))) hip
  have himm : P.ι im ∈ bowenBall G.finv (Tm + 1) x εm :=
    hmono _ _ _ ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))) him
  obtain ⟨hRp0, hRp1, hRp2⟩ := hRpspec x Tp (OrbitDatum.ofMem hipp) rfl le_rfl
  obtain ⟨hRm0, hRm1, hRm2⟩ := hRmspec x Tm (OrbitDatum.ofMem himm) rfl le_rfl
  simp only [OrbitDatum.ofMem_idx] at hRp0 hRp1 hRp2 hRm0 hRm1 hRm2
  -- the mesh at this input
  have hh_eq : mesh (j, ip, im, Tp, Tm, r) =
      min (min (Rp (ip, Tp)) (Rm (im, Tm))) 1 * r / 8 := by rw [hmesh_def]
  generalize hhdef : mesh (j, ip, im, Tp, Tm, r) = h at hh_eq
  have hmin1 : min (min (Rp (ip, Tp)) (Rm (im, Tm))) 1 ≤ 1 := min_le_right _ _
  have hminp : min (min (Rp (ip, Tp)) (Rm (im, Tm))) 1 ≤ Rp (ip, Tp) :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hminm : min (min (Rp (ip, Tp)) (Rm (im, Tm))) 1 ≤ Rm (im, Tm) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hmin0 : 0 < min (min (Rp (ip, Tp)) (Rm (im, Tm))) 1 :=
    lt_min (lt_min hRp0 hRm0) one_pos
  have hh0 : 0 < h := by rw [hh_eq]; positivity
  have hh1 : h ≤ r / 8 := by rw [hh_eq]; nlinarith
  have hhp : (h : ℝ) ≤ Rp (ip, Tp) * r / 8 := by
    have : h ≤ Rp (ip, Tp) * r / 8 := by rw [hh_eq]; nlinarith
    exact_mod_cast this
  have hhm : (h : ℝ) ≤ Rm (im, Tm) * r / 8 := by
    have : h ≤ Rm (im, Tm) * r / 8 := by rw [hh_eq]; nlinarith
    exact_mod_cast this
  have hh0' : (0 : ℝ) < h := by exact_mod_cast hh0
  have hhδ : (h : ℝ) ≤ δc := by
    have : (h : ℝ) ≤ r / 8 := by exact_mod_cast hh1
    linarith
  obtain ⟨hdom, hout⟩ := hnetx j r h hr0' hr2 hball hh0 hh1 Tp Tm hTp hTm
    (OrbitDatum.ofMem hip1) (OrbitDatum.ofMem him1) rfl le_rfl rfl le_rfl
  simp only [OrbitDatum.ofMem_idx] at hdom hout
  have hcovx := hcov x hxQ εx h hεx0 hεxδ hh0' hhδ
  have hRp1' : C₁ * G.scalePlus (ρ / 2) Tp x ≤ c₁ * Rp (ip, Tp) :=
    mul_le_mul hc₁.le hRp1 (G.scalePlus_pos _ _ _).le hc₁0.le
  have hRm1' : C₁ * G.scaleMinus (ρ / 2) Tm x ≤ c₁ * Rm (im, Tm) :=
    mul_le_mul hc₁.le hRm1 (G.scaleMinus_pos _ _ _).le hc₁0.le
  -- plaques lie in the small closed ball
  have hplq : ∀ k, G.plaque k εx x ⊆ Metric.closedBall x (r / 2) := by
    intro k w hw
    have hw' : w ∈ G.W k x ∧ G.dW k x w < εx := hw
    rw [Metric.mem_closedBall']
    calc dist x w ≤ G.CLeaf * G.dW k x w :=
          G.dist_le_CLeaf_mul_dW k x w hw'.1 (hw'.2.trans_le hεxr)
      _ ≤ G.CLeaf * εx := by gcongr; exact hw'.2.le
      _ ≤ r / 2 := hCεx
  rw [hnbhd_def]
  dsimp only
  rw [hhdef]
  refine ⟨by rw [Part.map_Dom]; exact hdom, fun out' hmem ↦ ?_⟩
  obtain ⟨out, hmemnet, rfl⟩ := (Part.mem_map_iff _).mp hmem
  obtain ⟨hnear, hcover, hbrk⟩ := hout out hmemnet
  rw [hpost_def]
  dsimp only
  have hnear' : ∀ e ∈ out, dist (E.pIdx e.1) x < δc := fun e he ↦ (hnear e he).trans_le hr3
  refine ⟨?_, ?_, ?_, ?_, hRp0, hRp1, hRp2, hRm0, hRm1, hRm2⟩
  · -- cs cover
    intro w hw
    obtain ⟨e, he, hwe⟩ := Set.mem_iUnion₂.mp (hcover (hplq .cs hw))
    have hpw : dist (E.pIdx e.1) w < h := by rw [dist_comm]; exact Metric.mem_ball.mp hwe
    obtain ⟨⟨-, hdW⟩, hbr, hcmp⟩ := (hcovx (E.pIdx e.1) (hnear' e he)).1 w hw hpw
    refine Set.mem_iUnion₂.mpr ⟨(e.2.1, (1 + c₁) * Rp (ip, Tp)), List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    change w ∈ Metric.ball (P.ι e.2.1) (((1 + c₁) * Rp (ip, Tp) : ℚ) : ℝ)
    rw [Metric.mem_ball]
    have h1 : dist w (G.bracketS (E.pIdx e.1) x) < (Rp (ip, Tp) : ℝ) := by
      rw [← hbr, dist_comm]
      calc dist (G.bracketS (E.pIdx e.1) w) w
          ≤ G.CLeaf * G.dW .cs w (G.bracketS (E.pIdx e.1) w) := hcmp
        _ ≤ G.CLeaf * (κ * dist (E.pIdx e.1) w) := by gcongr
        _ < G.CLeaf * (κ * h) := by gcongr
        _ ≤ G.CLeaf * (κ * (Rp (ip, Tp) * r / 8)) := by gcongr
        _ = Rp (ip, Tp) * (G.CLeaf * κ * r / 8) := by ring
        _ ≤ Rp (ip, Tp) * 1 := by gcongr
        _ = Rp (ip, Tp) := mul_one _
    have h2 := (hbrk e he).1
    push_cast
    calc dist w (P.ι e.2.1)
        ≤ dist w (G.bracketS (E.pIdx e.1) x) + dist (G.bracketS (E.pIdx e.1) x) (P.ι e.2.1) :=
          dist_triangle _ _ _
      _ < Rp (ip, Tp) + c₁ * Rp (ip, Tp) := by rw [dist_comm (G.bracketS _ _)]; linarith
      _ = (1 + c₁) * Rp (ip, Tp) := by ring
  · -- cs containment
    intro y hy
    obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    have hyb' : dist y (P.ι e.2.1) < (((1 + c₁) * Rp (ip, Tp) : ℚ) : ℝ) := Metric.mem_ball.mp hyb
    push_cast at hyb'
    have hcen := (hcovx (E.pIdx e.1) (hnear' e he)).2.1
    refine Metric.mem_thickening_iff.mpr ⟨_, hcen, ?_⟩
    have h2 := (hbrk e he).1
    calc dist y (G.bracketS (E.pIdx e.1) x)
        ≤ dist y (P.ι e.2.1) + dist (P.ι e.2.1) (G.bracketS (E.pIdx e.1) x) := dist_triangle _ _ _
      _ < (1 + c₁) * Rp (ip, Tp) + c₁ * Rp (ip, Tp) := by linarith
      _ = (1 + 2 * c₁) * Rp (ip, Tp) := by ring
      _ ≤ (1 + 2 * c₁) * G.scalePlus ρ Tp x := by gcongr
  · -- cu cover
    intro w hw
    obtain ⟨e, he, hwe⟩ := Set.mem_iUnion₂.mp (hcover (hplq .cu hw))
    have hpw : dist (E.pIdx e.1) w < h := by rw [dist_comm]; exact Metric.mem_ball.mp hwe
    obtain ⟨⟨-, hdW⟩, hbr, hcmp⟩ := (hcovx (E.pIdx e.1) (hnear' e he)).2.2.1 w hw hpw
    refine Set.mem_iUnion₂.mpr ⟨(e.2.2, (1 + c₁) * Rm (im, Tm)), List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    change w ∈ Metric.ball (P.ι e.2.2) (((1 + c₁) * Rm (im, Tm) : ℚ) : ℝ)
    rw [Metric.mem_ball]
    have h1 : dist w (G.bracketU x (E.pIdx e.1)) < (Rm (im, Tm) : ℝ) := by
      rw [← hbr, dist_comm]
      calc dist (G.bracketU w (E.pIdx e.1)) w
          ≤ G.CLeaf * G.dW .cu w (G.bracketU w (E.pIdx e.1)) := hcmp
        _ ≤ G.CLeaf * (κ * dist (E.pIdx e.1) w) := by gcongr
        _ < G.CLeaf * (κ * h) := by gcongr
        _ ≤ G.CLeaf * (κ * (Rm (im, Tm) * r / 8)) := by gcongr
        _ = Rm (im, Tm) * (G.CLeaf * κ * r / 8) := by ring
        _ ≤ Rm (im, Tm) * 1 := by gcongr
        _ = Rm (im, Tm) := mul_one _
    have h2 := (hbrk e he).2
    push_cast
    calc dist w (P.ι e.2.2)
        ≤ dist w (G.bracketU x (E.pIdx e.1)) + dist (G.bracketU x (E.pIdx e.1)) (P.ι e.2.2) :=
          dist_triangle _ _ _
      _ < Rm (im, Tm) + c₁ * Rm (im, Tm) := by rw [dist_comm (G.bracketU _ _)]; linarith
      _ = (1 + c₁) * Rm (im, Tm) := by ring
  · -- cu containment
    intro y hy
    obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
    have hyb' : dist y (P.ι e.2.2) < (((1 + c₁) * Rm (im, Tm) : ℚ) : ℝ) := Metric.mem_ball.mp hyb
    push_cast at hyb'
    have hcen := (hcovx (E.pIdx e.1) (hnear' e he)).2.2.2
    refine Metric.mem_thickening_iff.mpr ⟨_, hcen, ?_⟩
    have h2 := (hbrk e he).2
    calc dist y (G.bracketU x (E.pIdx e.1))
        ≤ dist y (P.ι e.2.2) + dist (P.ι e.2.2) (G.bracketU x (E.pIdx e.1)) := dist_triangle _ _ _
      _ < (1 + c₁) * Rm (im, Tm) + c₁ * Rm (im, Tm) := by linarith
      _ = (1 + 2 * c₁) * Rm (im, Tm) := by ring
      _ ≤ (1 + 2 * c₁) * G.scaleMinus ρ Tm x := by gcongr

end EffectiveGeodesicData

end Kolmogorov.PointToSet
