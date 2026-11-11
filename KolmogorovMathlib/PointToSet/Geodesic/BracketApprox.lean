/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.BracketApprox.Geometry

/-!
# Local products from finite orbit data (geodesic blueprint, Chapter E)

The programs of the nodes `geo:bracket-approx` (OTL `lem:local_product_approximator`) and
`geo:net-approx` (OTL `lem:net_local_product_approximator`) of
`geodesic_upper_bound_blueprint.md`; the geometric steps (bracket constructions, error bounds,
uniqueness of the decoded point, `SmallPlaques`) are in `BracketApprox/Geometry.lean`.

The integral scales of the whole argument, in bits (decision D2), are
`scalePlus ρ T x = 2 ^ (-(S_T u⁺(x) - ρ T))` and `scaleMinus ρ T x = 2 ^ (-(S_T u⁻(x) - ρ T))`,
where `S_T u⁺(x) = birkhoffSum f u⁺ T x` is the forward accumulated unstable rate on `[0, T]`
and `S_T u⁻(x)` the backward accumulated stable rate; they are defined in `OrbitData.lean`.
Orbit data enter the statements as `OrbitDatum`s (`OrbitData.lean`): the programs take the bare
ideal index `d.idx`, and correctness is asserted for every datum of order `T + 1` and
tolerance at most the decoder tolerance.

Quantifier structure of the bracket lemma, following OTL: the program and the constants
`ε, C₁` depend only on `ρ` and the endpoint set `Pp` (through the local product constants near
`Pp`, the leafwise contraction radius and the decoder tolerance); the admissible radius `δ`
about the base point `x` is the only point-dependent quantity, and it never depends on the
duration `T` (decision D7). Uniformity in the marked point `p` is what the net lemma needs.

The compact plaques of marked points must lie inside the expansivity plaques of the
decoder; this is recorded as the explicit hypothesis `SmallPlaques` rather than as a field of
`GeodesicReconstructionData`, since the expansivity scale depends on the compact set `Q`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### `geo:bracket-approx`: the algorithms -/

/-- Local-product approximation from forward orbit data (OTL `lem:local_product_approximator`,
forward half). For compact regular `Pp` and loss `ρ > 0` there are a tolerance `ε`, a constant
`C₁`, a plaque threshold `ε₀`, and one `B`-partial recursive program `brS` such that, whenever
the compact plaques of the marked points of a neighborhood of `Pp` are `ε₀`-small:
for every regular `x` there is an admissible radius `δ` such that for every marked
index `kp` within `δ` of `x`, every duration `T` with `φ T x ∈ Pp` and every forward orbit
datum `d` of order `T + 1` and tolerance at most `ε`, the program halts on `(kp, d.idx, T)` with
an ideal index within `C₁ E₊(ρ)` of `[pIdx kp, x]_s`. Blueprint node `geo:bracket-approx`. -/
theorem bracket_approx_forward {Pp : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    {Px : Set X} (hPx : IsCompact Px) (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ brS : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} brS ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (T : ℝ) x ∈ Pp →
              ∀ d : OrbitDatum P G.f x, d.order = T + 1 → d.tol ≤ ε →
                (brS (kp, d.idx, T)).Dom ∧
                  ∀ q ∈ brS (kp, d.idx, T),
                    dist (P.ι q) (G.bracketS (E.pIdx kp) x) ≤ C₁ * G.scalePlus ρ T x) := by
  have hL : 0 < G.L := by linarith [G.one_le_L]
  obtain ⟨Q, hQ, hPQ, hQR⟩ := G.exists_compact_nhds_regular hPp hPpR
  -- uniqueness constants
  obtain ⟨a₀, ha₀, ε₀, hε₀, δ₃, hδ₃, huniq⟩ := E.shadowSet_subsingleton_of_mem hPx hPxR
  -- the decoder tolerance
  obtain ⟨ρ', hρ'0, hρ'a⟩ := exists_rat_btwn (show (0 : ℝ) < a₀ / (2 * G.L) by positivity)
  have hρ'a' : 2 * G.L * ρ' < a₀ := by
    rw [lt_div_iff₀ (by positivity)] at hρ'a
    linarith
  -- the geometric lemmas
  obtain ⟨ε₁, hε₁, η₁, hη₁, r, hr, hrε, hmem⟩ :=
    E.bracket_construction_mem_shadowSet hPp hPpR ρ' (by exact_mod_cast hρ'0) ε₀ hε₀
  obtain ⟨C', hC', η₂, hη₂, herr⟩ := E.bracket_construction_error hPp hPpR hρ
  -- the certificate threshold for the future marked point, and the precision scheme
  obtain ⟨η₀, hη₀0, hη₀⟩ := exists_rat_btwn (show (0 : ℝ) < min η₁ η₂ / 2 by positivity)
  obtain ⟨N, hN⟩ := G.exists_nat_dyadicRadius_le_scalePlus hρ.le
  -- the decoder
  obtain ⟨loc, hloc, hspec⟩ := E.shadowSet_decoder ρ'
  -- the search for the future marked point: a certified distance to `φ T (ι i)`
  obtain ⟨b₁, hb₁c, hb₁⟩ := IsRepresentedFamilyIn.names_uniform E.presentation
    E.flow_represented (x := P.ι) (a := fun i _ ↦ i) (fun i ↦ isCauchyName_const P i)
    ComputableIn.fst
  obtain ⟨aP, haPc, haP⟩ := E.pIdx_names
  have hv : IsComputableRealFamilyIn B fun w : (ℕ × ℕ) × ℕ ↦
      dist (E.pIdx w.2) (G.φ ((w.1.2 : ℚ) : ℝ) (P.ι w.1.1)) :=
    isComputableRealFamilyIn_dist_of_names E.presentation
      (x := fun w : (ℕ × ℕ) × ℕ ↦ E.pIdx w.2) (a := fun w ↦ aP w.2) (fun w ↦ haP w.2)
      (haPc.comp ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn)
      (y := fun w ↦ G.φ ((w.1.2 : ℚ) : ℝ) (P.ι w.1.1)) (b := fun w ↦ b₁ (w.1.2 : ℚ) w.1.1)
      (fun w ↦ hb₁ _ _)
      (hb₁c.comp (((ComputableReals.computable_natCastRat.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
          Computable.snd).computableIn)
  have hcert : IsREIn B fun w : (ℕ × ℕ) × ℕ ↦
      dist (E.pIdx w.2) (G.φ ((w.1.2 : ℚ) : ℝ) (P.ι w.1.1)) < (η₀ : ℝ) :=
    (birkhoff_computableIn_lt B _ hv).comp
      (Computable.id.pair (Computable.const η₀)).computableIn
  obtain ⟨srch, hsrch, hsdom, hssound⟩ := hcert.exists_partrecIn_choice
  -- the program: search `kq`, then decode at precision `N T`
  let brS : ℕ × ℕ × ℕ →. ℕ := fun d ↦
    (srch d.2).bind fun kq ↦ loc (d.1, r, d.2.1, d.2.2, kq, N * d.2.2)
  have hbrS : PartrecIn {charOracle B} brS := by
    refine PartrecIn.bind (hsrch.comp Computable.snd.computableIn) ?_
    have hmap : Computable fun v : (ℕ × ℕ × ℕ) × ℕ ↦
        (v.1.1, r, v.1.2.1, v.1.2.2, v.2, N * v.1.2.2) :=
      (Computable.fst.comp Computable.fst).pair ((Computable.const r).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
            (Computable.snd.pair (Primrec.nat_mul.to_comp.comp (Computable.const N)
              (Computable.snd.comp (Computable.snd.comp Computable.fst)))))))
    exact hloc.comp hmap.computableIn
  refine ⟨min ε₁ (η₀ / G.L), by positivity, C' + 1, by positivity, ε₀, hε₀, Q, hQ, hPQ, hQR,
    brS, hbrS, fun _ x hx ↦ ?_⟩
  obtain ⟨δ₁, hδ₁, hmem'⟩ := hmem x (hPxR hx)
  obtain ⟨δ₂, hδ₂, herr'⟩ := herr x (hPxR hx)
  refine ⟨min δ₁ (min δ₂ δ₃), by positivity, fun kp hkp T hT d hdT hdtol ↦ ?_⟩
  have hi := d.mem_order hdT hdtol
  generalize d.idx = i at hi ⊢
  have hkp₁ : dist (E.pIdx kp) x < δ₁ := lt_of_lt_of_le hkp (min_le_left _ _)
  have hkp₂ : dist (E.pIdx kp) x < δ₂ :=
    lt_of_lt_of_le hkp ((min_le_right _ _).trans (min_le_left _ _))
  have hkp₃ : dist (E.pIdx kp) x < δ₃ :=
    lt_of_lt_of_le hkp ((min_le_right _ _).trans (min_le_right _ _))
  have hi₁ : P.ι i ∈ bowenBall G.f (T + 1) x ε₁ :=
    bowenBall_mono_radius G.f (T + 1) x (min_le_left _ _) hi
  -- a certified `kq` is close to `φ T x`
  have hgood : ∀ kq, kq ∈ srch (i, T) → dist (E.pIdx kq) (G.φ (T : ℝ) x) < min η₁ η₂ := by
    intro kq hkq
    have h1 := hssound (i, T) kq hkq
    simp only [Rat.cast_natCast] at h1
    have h2 : dist (G.φ (T : ℝ) (P.ι i)) (G.φ (T : ℝ) x) < G.L * min ε₁ (η₀ / G.L) := by
      rw [dist_comm]
      exact G.toFlowData.dist_flow_lt_of_mem_bowenBall hi (Nat.cast_nonneg T) le_rfl
    have h3 : G.L * min ε₁ (η₀ / G.L) ≤ η₀ := by
      calc G.L * min ε₁ (η₀ / G.L) ≤ G.L * (η₀ / G.L) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le
        _ = η₀ := by field_simp
    calc dist (E.pIdx kq) (G.φ (T : ℝ) x)
        ≤ dist (E.pIdx kq) (G.φ (T : ℝ) (P.ι i)) + dist (G.φ (T : ℝ) (P.ι i)) (G.φ (T : ℝ) x) :=
          dist_triangle _ _ _
      _ < η₀ + η₀ := add_lt_add h1 (h2.trans_le h3)
      _ < min η₁ η₂ := by linarith
  have hy : ∀ kq, kq ∈ srch (i, T) →
      G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)) ∈
        E.shadowSet ρ' r kp i T kq := fun kq hkq ↦
    hmem' kp hkp₁ T hT i hi₁ kq ((hgood kq hkq).trans_le (min_le_left _ _))
  have hss : ∀ kq, (E.shadowSet ρ' r kp i T kq).Subsingleton := fun kq ↦
    huniq ρ' (by exact_mod_cast hρ'0.le) hρ'a' x hx kp hkp₃ r hr hrε i T kq
  constructor
  · -- the search halts (density) and so does the decoder
    obtain ⟨kq₀, hkq₀⟩ : ∃ kq, dist (E.pIdx kq) (G.φ ((T : ℚ) : ℝ) (P.ι i)) < (η₀ : ℝ) := by
      obtain ⟨y, ⟨kq, rfl⟩, hy⟩ := E.pIdx_dense.exists_dist_lt (G.φ ((T : ℚ) : ℝ) (P.ι i))
        (ε := (η₀ : ℝ)) (by exact_mod_cast hη₀0)
      exact ⟨kq, by rwa [dist_comm]⟩
    have hsd : (srch (i, T)).Dom := (hsdom (i, T)).mpr ⟨kq₀, hkq₀⟩
    obtain ⟨kq, hkq⟩ := Part.dom_iff_mem.mp hsd
    have hld := (hspec kp r i T kq (N * T) hr (hss kq) _ (hy kq hkq)).1
    obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp hld
    exact Part.dom_iff_mem.mpr ⟨q, Part.mem_bind_iff.mpr ⟨kq, hkq, hq⟩⟩
  · intro q hq
    obtain ⟨kq, hkq, hq'⟩ := Part.mem_bind_iff.mp hq
    have h1 := (hspec kp r i T kq (N * T) hr (hss kq) _ (hy kq hkq)).2 q hq'
    have h2 := herr' kp hkp₂ T hT kq ((hgood kq hkq).trans_le (min_le_right _ _))
    calc dist (P.ι q) (G.bracketS (E.pIdx kp) x)
        ≤ dist (P.ι q)
            (G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq))) +
          dist (G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)))
            (G.bracketS (E.pIdx kp) x) := dist_triangle _ _ _
      _ ≤ G.scalePlus ρ T x + C' * G.scalePlus ρ T x :=
          add_le_add (h1.le.trans (hN T x)) h2
      _ = (C' + 1) * G.scalePlus ρ T x := by ring

/-- Local-product approximation from backward orbit data (reversed half): the program `brU`
takes `(kp, d.idx, T)` with `d` a backward orbit datum of order `T + 1` and tolerance at most
`ε`, and `φ (-T) x ∈ Pm`, and outputs an ideal index within `C₁ E₋(ρ)` of `[x, pIdx kp]_u`.
Anchored on the compact stable plaque of `p`. Blueprint node `geo:bracket-approx`. -/
theorem bracket_approx_backward {Pm : Set X} (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg)
    {Px : Set X} (hPx : IsCompact Px) (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ brU : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} brU ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (-(T : ℝ)) x ∈ Pm →
              ∀ d : OrbitDatum P G.finv x, d.order = T + 1 → d.tol ≤ ε →
                (brU (kp, d.idx, T)).Dom ∧
                  ∀ q ∈ brU (kp, d.idx, T),
                    dist (P.ι q) (G.bracketU x (E.pIdx kp)) ≤ C₁ * G.scaleMinus ρ T x) := by
  have hL : 0 < G.L := by linarith [G.one_le_L]
  obtain ⟨Q, hQ, hPQ, hQR⟩ := G.exists_compact_nhds_regular hPm hPmR
  obtain ⟨a₀, ha₀, ε₀, hε₀, δ₃, hδ₃, huniq⟩ := E.shadowSetBackward_subsingleton_of_mem hPx hPxR
  obtain ⟨ρ', hρ'0, hρ'a⟩ := exists_rat_btwn (show (0 : ℝ) < a₀ / (2 * G.L) by positivity)
  have hρ'a' : 2 * G.L * ρ' < a₀ := by
    rw [lt_div_iff₀ (by positivity)] at hρ'a
    linarith
  obtain ⟨ε₁, hε₁, η₁, hη₁, r, hr, hrε, hmem⟩ :=
    E.bracket_construction_mem_shadowSetBackward hPm hPmR ρ' (by exact_mod_cast hρ'0) ε₀ hε₀
  obtain ⟨C', hC', η₂, hη₂, herr⟩ := E.bracket_construction_error_backward hPm hPmR hρ
  obtain ⟨η₀, hη₀0, hη₀⟩ := exists_rat_btwn (show (0 : ℝ) < min η₁ η₂ / 2 by positivity)
  obtain ⟨N, hN⟩ := G.exists_nat_dyadicRadius_le_scaleMinus hρ.le
  obtain ⟨loc, hloc, hspec⟩ := E.shadowSetBackward_decoder ρ'
  obtain ⟨b₁, hb₁c, hb₁⟩ := IsRepresentedFamilyIn.names_uniform E.presentation
    E.flow_represented (x := P.ι) (a := fun i _ ↦ i) (fun i ↦ isCauchyName_const P i)
    ComputableIn.fst
  obtain ⟨aP, haPc, haP⟩ := E.pIdx_names
  have hv : IsComputableRealFamilyIn B fun w : (ℕ × ℕ) × ℕ ↦
      dist (E.pIdx w.2) (G.φ ((-(w.1.2 : ℚ) : ℚ) : ℝ) (P.ι w.1.1)) :=
    isComputableRealFamilyIn_dist_of_names E.presentation
      (x := fun w : (ℕ × ℕ) × ℕ ↦ E.pIdx w.2) (a := fun w ↦ aP w.2) (fun w ↦ haP w.2)
      (haPc.comp ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn)
      (y := fun w ↦ G.φ ((-(w.1.2 : ℚ) : ℚ) : ℝ) (P.ι w.1.1))
      (b := fun w ↦ b₁ (-(w.1.2 : ℚ)) w.1.1) (fun w ↦ hb₁ _ _)
      (hb₁c.comp (((ComputableReals.computable_ratNeg.comp
        (ComputableReals.computable_natCastRat.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst)))).pair
        (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
          Computable.snd).computableIn)
  have hcert : IsREIn B fun w : (ℕ × ℕ) × ℕ ↦
      dist (E.pIdx w.2) (G.φ ((-(w.1.2 : ℚ) : ℚ) : ℝ) (P.ι w.1.1)) < (η₀ : ℝ) :=
    (birkhoff_computableIn_lt B _ hv).comp
      (Computable.id.pair (Computable.const η₀)).computableIn
  obtain ⟨srch, hsrch, hsdom, hssound⟩ := hcert.exists_partrecIn_choice
  let brU : ℕ × ℕ × ℕ →. ℕ := fun d ↦
    (srch d.2).bind fun kq ↦ loc (d.1, r, d.2.1, d.2.2, kq, N * d.2.2)
  have hbrU : PartrecIn {charOracle B} brU := by
    refine PartrecIn.bind (hsrch.comp Computable.snd.computableIn) ?_
    have hmap : Computable fun v : (ℕ × ℕ × ℕ) × ℕ ↦
        (v.1.1, r, v.1.2.1, v.1.2.2, v.2, N * v.1.2.2) :=
      (Computable.fst.comp Computable.fst).pair ((Computable.const r).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
            (Computable.snd.pair (Primrec.nat_mul.to_comp.comp (Computable.const N)
              (Computable.snd.comp (Computable.snd.comp Computable.fst)))))))
    exact hloc.comp hmap.computableIn
  refine ⟨min ε₁ (η₀ / G.L), by positivity, C' + 1, by positivity, ε₀, hε₀, Q, hQ, hPQ, hQR,
    brU, hbrU, fun _ x hx ↦ ?_⟩
  obtain ⟨δ₁, hδ₁, hmem'⟩ := hmem x (hPxR hx)
  obtain ⟨δ₂, hδ₂, herr'⟩ := herr x (hPxR hx)
  refine ⟨min δ₁ (min δ₂ δ₃), by positivity, fun kp hkp T hT d hdT hdtol ↦ ?_⟩
  have hi := d.mem_order hdT hdtol
  generalize d.idx = i at hi ⊢
  have hkp₁ : dist (E.pIdx kp) x < δ₁ := lt_of_lt_of_le hkp (min_le_left _ _)
  have hkp₂ : dist (E.pIdx kp) x < δ₂ :=
    lt_of_lt_of_le hkp ((min_le_right _ _).trans (min_le_left _ _))
  have hkp₃ : dist (E.pIdx kp) x < δ₃ :=
    lt_of_lt_of_le hkp ((min_le_right _ _).trans (min_le_right _ _))
  have hi₁ : P.ι i ∈ bowenBall G.finv (T + 1) x ε₁ :=
    bowenBall_mono_radius G.finv (T + 1) x (min_le_left _ _) hi
  have hgood : ∀ kq, kq ∈ srch (i, T) → dist (E.pIdx kq) (G.φ (-(T : ℝ)) x) < min η₁ η₂ := by
    intro kq hkq
    have h1 := hssound (i, T) kq hkq
    simp only [Rat.cast_neg, Rat.cast_natCast] at h1
    have h2 : dist (G.φ (-(T : ℝ)) (P.ι i)) (G.φ (-(T : ℝ)) x) < G.L * min ε₁ (η₀ / G.L) := by
      rw [dist_comm]
      exact G.toFlowData.dist_flow_lt_of_mem_bowenBall_finv hi le_rfl
        (neg_nonpos.mpr (Nat.cast_nonneg T))
    have h3 : G.L * min ε₁ (η₀ / G.L) ≤ η₀ := by
      calc G.L * min ε₁ (η₀ / G.L) ≤ G.L * (η₀ / G.L) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hL.le
        _ = η₀ := by field_simp
    calc dist (E.pIdx kq) (G.φ (-(T : ℝ)) x)
        ≤ dist (E.pIdx kq) (G.φ (-(T : ℝ)) (P.ι i)) +
            dist (G.φ (-(T : ℝ)) (P.ι i)) (G.φ (-(T : ℝ)) x) := dist_triangle _ _ _
      _ < η₀ + η₀ := add_lt_add h1 (h2.trans_le h3)
      _ < min η₁ η₂ := by linarith
  have hy : ∀ kq, kq ∈ srch (i, T) →
      G.φ (T : ℝ) (G.bracketU (E.pIdx kq) (G.φ (-(T : ℝ)) (G.bracketU x (E.pIdx kp)))) ∈
        E.shadowSetBackward ρ' r kp i T kq := fun kq hkq ↦
    hmem' kp hkp₁ T hT i hi₁ kq ((hgood kq hkq).trans_le (min_le_left _ _))
  have hss : ∀ kq, (E.shadowSetBackward ρ' r kp i T kq).Subsingleton := fun kq ↦
    huniq ρ' (by exact_mod_cast hρ'0.le) hρ'a' x hx kp hkp₃ r hr hrε i T kq
  constructor
  · obtain ⟨kq₀, hkq₀⟩ : ∃ kq, dist (E.pIdx kq) (G.φ ((-(T : ℚ) : ℚ) : ℝ) (P.ι i)) < (η₀ : ℝ) := by
      obtain ⟨y, ⟨kq, rfl⟩, hy⟩ := E.pIdx_dense.exists_dist_lt
        (G.φ ((-(T : ℚ) : ℚ) : ℝ) (P.ι i)) (ε := (η₀ : ℝ)) (by exact_mod_cast hη₀0)
      exact ⟨kq, by rwa [dist_comm]⟩
    have hsd : (srch (i, T)).Dom := (hsdom (i, T)).mpr ⟨kq₀, hkq₀⟩
    obtain ⟨kq, hkq⟩ := Part.dom_iff_mem.mp hsd
    have hld := (hspec kp r i T kq (N * T) hr (hss kq) _ (hy kq hkq)).1
    obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp hld
    exact Part.dom_iff_mem.mpr ⟨q, Part.mem_bind_iff.mpr ⟨kq, hkq, hq⟩⟩
  · intro q hq
    obtain ⟨kq, hkq, hq'⟩ := Part.mem_bind_iff.mp hq
    have h1 := (hspec kp r i T kq (N * T) hr (hss kq) _ (hy kq hkq)).2 q hq'
    have h2 := herr' kp hkp₂ T hT kq ((hgood kq hkq).trans_le (min_le_right _ _))
    calc dist (P.ι q) (G.bracketU x (E.pIdx kp))
        ≤ dist (P.ι q)
            (G.φ (T : ℝ) (G.bracketU (E.pIdx kq) (G.φ (-(T : ℝ)) (G.bracketU x (E.pIdx kp))))) +
          dist (G.φ (T : ℝ) (G.bracketU (E.pIdx kq) (G.φ (-(T : ℝ)) (G.bracketU x (E.pIdx kp)))))
            (G.bracketU x (E.pIdx kp)) := dist_triangle _ _ _
      _ ≤ G.scaleMinus ρ T x + C' * G.scaleMinus ρ T x :=
          add_le_add (h1.le.trans (hN T x)) h2
      _ = (C' + 1) * G.scaleMinus ρ T x := by ring

/-- Both directions at once, with common `ε, C₁, ε₀` and a common admissible radius: the form
used by the net lemma. The forward output uses only the forward data and the backward output
only the backward data. Blueprint node `geo:bracket-approx`. -/
theorem bracket_approx {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {Px : Set X} (hPx : IsCompact Px)
    (hPxR : Px ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ brS brU : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} brS ∧ PartrecIn {charOracle B} brU ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ δ : ℝ, 0 < δ ∧
            ∀ kp, dist (E.pIdx kp) x < δ →
              (∀ T : ℕ, G.φ (T : ℝ) x ∈ Pp → ∀ d : OrbitDatum P G.f x, d.order = T + 1 →
                d.tol ≤ ε → (brS (kp, d.idx, T)).Dom ∧ ∀ q ∈ brS (kp, d.idx, T),
                  dist (P.ι q) (G.bracketS (E.pIdx kp) x) ≤ C₁ * G.scalePlus ρ T x) ∧
              (∀ T : ℕ, G.φ (-(T : ℝ)) x ∈ Pm → ∀ d : OrbitDatum P G.finv x, d.order = T + 1 →
                d.tol ≤ ε → (brU (kp, d.idx, T)).Dom ∧ ∀ q ∈ brU (kp, d.idx, T),
                  dist (P.ι q) (G.bracketU x (E.pIdx kp)) ≤ C₁ * G.scaleMinus ρ T x)) := by
  obtain ⟨ε₁, hε₁, C₁, hC₁, ε₀, hε₀, Q₁, hQ₁, hPQ₁, hQR₁, brS, hbrS, hS⟩ :=
    E.bracket_approx_forward hPp hPpR hPx hPxR hρ
  obtain ⟨ε₂, hε₂, C₂, hC₂, ε₀', hε₀', Q₂, hQ₂, hPQ₂, hQR₂, brU, hbrU, hU⟩ :=
    E.bracket_approx_backward hPm hPmR hPx hPxR hρ
  refine ⟨min ε₁ ε₂, by positivity, max C₁ C₂, by positivity, min ε₀ ε₀', by positivity,
    Q₁ ∪ Q₂, hQ₁.union hQ₂, ?_, Set.union_subset hQR₁ hQR₂, brS, brU, hbrS, hbrU,
    fun _ x hx ↦ ?_⟩
  · exact Set.union_subset (hPQ₁.trans (interior_mono Set.subset_union_left))
      (hPQ₂.trans (interior_mono Set.subset_union_right))
  obtain ⟨δ₁, hδ₁, h₁⟩ := hS (G.smallPlaques Q₁ ε₀) x hx
  obtain ⟨δ₂, hδ₂, h₂⟩ := hU (G.smallPlaques Q₂ ε₀') x hx
  refine ⟨min δ₁ δ₂, by positivity,
    fun kp hkp ↦ ⟨fun T hT d hdT hdtol ↦ ?_, fun T hT d hdT hdtol ↦ ?_⟩⟩
  · obtain ⟨hdom, hout⟩ := h₁ kp (lt_of_lt_of_le hkp (min_le_left _ _)) T hT d hdT
      (hdtol.trans (min_le_left _ _))
    exact ⟨hdom, fun q hq ↦ (hout q hq).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (G.scalePlus_pos ρ T x).le)⟩
  · obtain ⟨hdom, hout⟩ := h₂ kp (lt_of_lt_of_le hkp (min_le_right _ _)) T hT d hdT
      (hdtol.trans (min_le_right _ _))
    exact ⟨hdom, fun q hq ↦ (hout q hq).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (G.scaleMinus_pos ρ T x).le)⟩

/-! ### `geo:net-approx`: approximation on a marked net -/

omit E in
/-- A Lebesgue number for the inner boxes: every closed ball of radius `ℓ` lies in some inner
box (finite open cover of a compact space). Blueprint node `geo:net-approx` (localization). -/
theorem exists_lebesgue_innerBox :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ x : X, ∃ j, Metric.closedBall x ℓ ⊆ G.innerBox j := by
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric (s := (Set.univ : Set X))
    isCompact_univ G.isOpen_innerBox (by rw [G.innerBox_cover])
  refine ⟨δ / 2, by positivity, fun x ↦ ?_⟩
  obtain ⟨j, hj⟩ := hcov x (Set.mem_univ x)
  exact ⟨j, (Metric.closedBall_subset_ball (by linarith)).trans hj⟩

/-- Approximation on a marked net (OTL `lem:net_local_product_approximator`). With the data of
`bracket_approx` there is one `B`-partial recursive program `net` which, on input a box index
`j`, forward and backward orbit data `(ip, Tp)`, `(im, Tm)`, a radius `r` and a mesh `h`, lists
triples `(kp, q⁺, q⁻)`: marked indices `kp` within `2r` of `x`, whose `h`-balls cover
`closedBall x (r/2)`, together with the bracket approximations of `bracket_approx` for each of
them. Validity: `x` regular, `closedBall x (2r) ⊆ innerBox j` (available for `2r ≤ ℓ` by
`exists_lebesgue_innerBox`), `2r < δ` the admissible radius of `x`, `h ≤ r/8`, orbit data
`dp, dm` of orders `Tp + 1`, `Tm + 1` at tolerance at most `min ε (r/8)` (the program takes
their indices `ip = dp.idx`, `im = dm.idx`), and regular endpoints `φ Tp x ∈ Pp`,
`φ (-Tm) x ∈ Pm`.
The program covers the computably compact `closure (innerBox j)` by enumerated marked
points at mesh `h`, keeps those certified within `r` of the time-zero datum `ι ip` (dovetailing
the two semidecidable tests `dist < r` and `dist > 3r/4`), and runs both bracket programs on
each kept point; all kept points are admissible, so every run halts. The constant `C₁` is
independent of `h`, of the list length and of the index. Blueprint node `geo:net-approx`. -/
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
              ∀ (dp : OrbitDatum P G.f x) (dm : OrbitDatum P G.finv x),
                dp.order = Tp + 1 → dp.tol ≤ min ε (r / 8) →
                dm.order = Tm + 1 → dm.tol ≤ min ε (r / 8) →
                (net (j, dp.idx, dm.idx, Tp, Tm, r, h)).Dom ∧
                  ∀ out ∈ net (j, dp.idx, dm.idx, Tp, Tm, r, h),
                    (∀ e ∈ out, dist (E.pIdx e.1) x < 2 * r) ∧
                    Metric.closedBall x (r / 2) ⊆ ⋃ e ∈ out, Metric.ball (E.pIdx e.1) (h : ℝ) ∧
                    ∀ e ∈ out,
                      dist (P.ι e.2.1) (G.bracketS (E.pIdx e.1) x) ≤ C₁ * G.scalePlus ρ Tp x ∧
                      dist (P.ι e.2.2) (G.bracketU x (E.pIdx e.1)) ≤
                        C₁ * G.scaleMinus ρ Tm x) := by
  obtain ⟨ε, hε, C₁, hC₁, ε₀, hε₀, Q, hQ, hPQ, hQR, brS, brU, hbrS, hbrU, hbr⟩ :=
    E.bracket_approx hPp hPpR hPm hPmR hPx hPxR hρ
  obtain ⟨aP, haPc, haP⟩ := E.pIdx_names
  -- projections of the input `(j, ip, im, Tp, Tm, r, h)`
  have pip : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦ d.2.1 :=
    Computable.fst.comp Computable.snd
  have pim : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦ d.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have pTp : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦ d.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have pTm : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦ d.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      Computable.snd)))
  have pr : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦ d.2.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))))
  have ph : Computable fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦ d.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.snd))))
  -- (1) the c.e. predicate "`pIdx kp` lies within `15 r / 8` of `ι ip`", and its prefix lists
  have hv : IsComputableRealFamilyIn B fun w : (ℕ × ℚ) × ℕ ↦ dist (E.pIdx w.2) (P.ι w.1.1) :=
    isComputableRealFamilyIn_dist_of_names E.presentation
      (x := fun w : (ℕ × ℚ) × ℕ ↦ E.pIdx w.2) (a := fun w ↦ aP w.2) (fun w ↦ haP w.2)
      (haPc.comp ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn)
      (y := fun w ↦ P.ι w.1.1) (b := fun w _ ↦ w.1.1) (fun w ↦ isCauchyName_const P _)
      (Computable.fst.comp (Computable.fst.comp Computable.fst)).computableIn
  have hcert : IsREIn B fun w : (ℕ × ℚ) × ℕ ↦
      dist (E.pIdx w.2) (P.ι w.1.1) < ((15 / 8 * w.1.2 : ℚ) : ℝ) :=
    (birkhoff_computableIn_lt B _ hv).comp (Computable.id.pair
      (computable₂_ratMul.comp (Computable.const (15 / 8 : ℚ))
        (Computable.snd.comp Computable.fst))).computableIn
  obtain ⟨L, hLc, hLsound, hLmono, -, hLfin⟩ := hcert.exists_prefixList
  -- (2) the cover certificate, on `(input, stage)`
  have hball : IsCeOpenFamilyIn P B fun d : ℕ × ℚ ↦ {w | dist w (E.pIdx d.1) < (d.2 : ℝ)} :=
    isCeOpenFamilyIn_dist_lt E.presentation haP haPc
  have hU₁ : IsCeOpenFamilyIn P B fun dk : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ) × ℕ ↦
      {w | dist w (E.pIdx dk.2) < (dk.1.2.2.2.2.2.2 : ℝ)} :=
    hball.comp (Computable.snd.pair (ph.comp Computable.fst))
  have hU₂ := hU₁.biUnion_list
  have hLin : ComputableIn {charOracle B}
      fun dt : (Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ) × ℕ ↦
        L ((dt.1.2.1, dt.1.2.2.2.2.2.1), dt.2) :=
    hLc.comp (((pip.comp Computable.fst).pair (pr.comp Computable.fst)).pair
      Computable.snd).computableIn
  have hU₃ := hU₂.compIn (ComputableIn.fst.pair hLin)
  have hV : IsCeOpenFamilyIn P B fun d : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ ↦
      {w | ((3 / 4 * d.2.2.2.2.2.1 : ℚ) : ℝ) < dist w (P.ι d.2.1)} :=
    (isCeOpenFamilyIn_lt_dist E.presentation (w₀ := P.ι) (a := fun i _ ↦ i)
      (fun i ↦ isCauchyName_const P i) ComputableIn.fst).comp
      (pip.pair (computable₂_ratMul.comp (Computable.const (3 / 4 : ℚ)) pr))
  have hW := hU₃.union (hV.comp Computable.fst)
  have hcertW := (E.innerBox_cc.subset_ceOpen_isREIn hW).comp
    ((Computable.fst.comp Computable.fst).pair Computable.id).computableIn
  obtain ⟨srch, hsrch, hsdom, hssound⟩ := hcertW.exists_partrecIn_choice
  -- (3) running both bracket programs along the list
  let g : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ → ℕ →. ℕ × ℕ := fun d kp ↦
    (brS (kp, d.2.1, d.2.2.2.1)).bind fun qp ↦
      (brU (kp, d.2.2.1, d.2.2.2.2.1)).map fun qm ↦ (qp, qm)
  have hg : PartrecIn₂ {charOracle B} g := by
    refine PartrecIn.bind (hbrS.comp (Computable.snd.pair ((pip.comp Computable.fst).pair
      (pTp.comp Computable.fst))).computableIn) ?_
    exact PartrecIn.map (hbrU.comp ((Computable.snd.comp Computable.fst).pair
      ((pim.comp (Computable.fst.comp Computable.fst)).pair
        (pTm.comp (Computable.fst.comp Computable.fst)))).computableIn)
      ((Computable.snd.comp Computable.fst).pair Computable.snd).computableIn
  obtain ⟨run, hrun, hrundom, hrunspec⟩ := PartrecIn.exists_list_mapM hg
  let net : Fin G.nBoxes × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ →. List (ℕ × ℕ × ℕ) := fun d ↦
    (srch d).bind fun t ↦ run (d, L ((d.2.1, d.2.2.2.2.2.1), t))
  have hnet : PartrecIn {charOracle B} net := by
    refine PartrecIn.bind hsrch ?_
    exact hrun.comp (Computable.fst.computableIn.pair hLin)
  refine ⟨ε, hε, C₁, hC₁, ε₀, hε₀, Q, hQ, hPQ, hQR, net, hnet, fun _ x hx ↦ ?_⟩
  obtain ⟨δ, hδ, hbr'⟩ := hbr (G.smallPlaques Q ε₀) x hx
  refine ⟨δ, hδ,
    fun j r h hr hrδ hbox hh hhr Tp Tm hTp hTm dp dm hdpT hdptol hdmT hdmtol ↦ ?_⟩
  have hip := dp.mem_order hdpT hdptol
  have him := dm.mem_order hdmT hdmtol
  generalize dp.idx = ip at hip ⊢
  generalize dm.idx = im at him ⊢
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hhr' : (h : ℝ) ≤ r / 8 := by exact_mod_cast hhr
  -- the time-zero datum is within `r/8` of `x`
  have hipx : dist x (P.ι ip) < r / 8 := by
    have := mem_bowenBall_iff.mp hip 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at this
    exact this.trans_le (min_le_right _ _)
  -- listed marked points are within `2 r` of `x`, hence admissible
  have hkeep : ∀ t kp, kp ∈ L ((ip, r), t) → dist (E.pIdx kp) x < 2 * r := by
    intro t kp hkp
    have h1 := hLsound (ip, r) t kp hkp
    push_cast at h1
    have htri := dist_triangle (E.pIdx kp) (P.ι ip) x
    rw [dist_comm] at hipx
    linarith
  have hadm : ∀ t kp, kp ∈ L ((ip, r), t) →
      ((brS (kp, ip, Tp)).Dom ∧ ∀ q ∈ brS (kp, ip, Tp),
        dist (P.ι q) (G.bracketS (E.pIdx kp) x) ≤ C₁ * G.scalePlus ρ Tp x) ∧
      ((brU (kp, im, Tm)).Dom ∧ ∀ q ∈ brU (kp, im, Tm),
        dist (P.ι q) (G.bracketU x (E.pIdx kp)) ≤ C₁ * G.scaleMinus ρ Tm x) := by
    intro t kp hkp
    have hb := hbr' kp (by linarith [hkeep t kp hkp])
    exact ⟨hb.1 Tp hTp (OrbitDatum.ofMem hip) rfl (min_le_left _ _),
      hb.2 Tm hTm (OrbitDatum.ofMem him) rfl (min_le_left _ _)⟩
  have hgdom : ∀ t kp, kp ∈ L ((ip, r), t) → (g (j, ip, im, Tp, Tm, r, h) kp).Dom := by
    intro t kp hkp
    obtain ⟨⟨hdp, -⟩, ⟨hdm, -⟩⟩ := hadm t kp hkp
    obtain ⟨qp, hqp⟩ := Part.dom_iff_mem.mp hdp
    obtain ⟨qm, hqm⟩ := Part.dom_iff_mem.mp hdm
    exact Part.dom_iff_mem.mpr ⟨(qp, qm), Part.mem_bind_iff.mpr
      ⟨qp, hqp, (Part.mem_map_iff _).mpr ⟨qm, hqm, rfl⟩⟩⟩
  constructor
  · -- halting: a finite subcover of the part of the inner box near the datum
    have hK : IsCompact (closure (G.innerBox j) ∩ {w | dist w (P.ι ip) ≤ 3 / 4 * r}) :=
      isClosed_closure.isCompact.inter_right
        (isClosed_le (continuous_id.dist continuous_const) continuous_const)
    have hcov : closure (G.innerBox j) ∩ {w | dist w (P.ι ip) ≤ 3 / 4 * r} ⊆
        ⋃ kp ∈ {kp | dist (E.pIdx kp) (P.ι ip) < ((15 / 8 * r : ℚ) : ℝ)},
          Metric.ball (E.pIdx kp) (h : ℝ) := by
      intro w hw
      obtain ⟨y, ⟨kp, rfl⟩, hy⟩ := E.pIdx_dense.exists_dist_lt w (ε := (h : ℝ)) hh'
      have hw' : dist w (P.ι ip) ≤ 3 / 4 * r := hw.2
      refine Set.mem_iUnion₂.mpr ⟨kp, ?_, Metric.mem_ball.mpr hy⟩
      change dist (E.pIdx kp) (P.ι ip) < ((15 / 8 * r : ℚ) : ℝ)
      push_cast
      have htri := dist_triangle (E.pIdx kp) w (P.ι ip)
      rw [dist_comm] at hy
      linarith
    obtain ⟨F, hFE, hFfin, hKF⟩ :=
      hK.elim_finite_subcover_image (fun kp _ ↦ Metric.isOpen_ball) hcov
    obtain ⟨t, ht⟩ := hLfin (ip, r) hFfin.toFinset fun kp hkp ↦ hFE (hFfin.mem_toFinset.mp hkp)
    have hcertt : closure (G.innerBox j) ⊆
        (⋃ kp ∈ L ((ip, r), t), {w | dist w (E.pIdx kp) < (h : ℝ)}) ∪
          {w | ((3 / 4 * r : ℚ) : ℝ) < dist w (P.ι ip)} := by
      intro w hw
      by_cases hwd : dist w (P.ι ip) ≤ 3 / 4 * r
      · obtain ⟨kp, hkp, hwkp⟩ := Set.mem_iUnion₂.mp (hKF ⟨hw, hwd⟩)
        exact Or.inl (Set.mem_iUnion₂.mpr ⟨kp, ht kp (hFfin.mem_toFinset.mpr hkp), hwkp⟩)
      · refine Or.inr ?_
        change ((3 / 4 * r : ℚ) : ℝ) < dist w (P.ι ip)
        push_cast
        exact not_le.mp hwd
    have hsd : (srch (j, ip, im, Tp, Tm, r, h)).Dom := (hsdom _).mpr ⟨t, hcertt⟩
    obtain ⟨t', ht'⟩ := Part.dom_iff_mem.mp hsd
    have hrd : (run ((j, ip, im, Tp, Tm, r, h), L ((ip, r), t'))).Dom :=
      (hrundom _ _).mpr fun kp hkp ↦ hgdom t' kp hkp
    obtain ⟨out, hout⟩ := Part.dom_iff_mem.mp hrd
    exact Part.dom_iff_mem.mpr ⟨out, Part.mem_bind_iff.mpr ⟨t', ht', hout⟩⟩
  · -- correctness of every output
    intro out hout
    obtain ⟨t, ht, hout'⟩ := Part.mem_bind_iff.mp hout
    obtain ⟨hmap, hmem⟩ := hrunspec _ _ out hout'
    have hL' : ∀ e ∈ out, e.1 ∈ L ((ip, r), t) := fun e he ↦ by
      rw [← hmap]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    refine ⟨fun e he ↦ hkeep t e.1 (hL' e he), ?_, fun e he ↦ ?_⟩
    · intro w hw
      have hcertt := hssound _ t ht
      have hwin : w ∈ closure (G.innerBox j) :=
        subset_closure (hbox (Metric.closedBall_subset_closedBall (by linarith) hw))
      rcases hcertt hwin with hw1 | hw2
      · obtain ⟨kp, hkp, hwkp⟩ := Set.mem_iUnion₂.mp hw1
        have hkp' : kp ∈ out.map Prod.fst := by
          rw [hmap]
          exact hkp
        obtain ⟨e, he, hekp⟩ := List.mem_map.mp hkp'
        refine Set.mem_iUnion₂.mpr ⟨e, he, ?_⟩
        change dist w (E.pIdx e.1) < (h : ℝ)
        rw [hekp]
        exact hwkp
      · exfalso
        have h2 : ((3 / 4 * r : ℚ) : ℝ) < dist w (P.ι ip) := hw2
        push_cast at h2
        have hwx : dist w x ≤ r / 2 := hw
        have htri := dist_triangle w x (P.ι ip)
        linarith
    · obtain ⟨⟨-, hp⟩, ⟨-, hm⟩⟩ := hadm t e.1 (hL' e he)
      obtain ⟨qp, hqp, hq⟩ := Part.mem_bind_iff.mp (hmem e he)
      obtain ⟨qm, hqm, hqe⟩ := (Part.mem_map_iff _).mp hq
      rw [← hqe]
      exact ⟨hp qp hqp, hm qm hqm⟩

omit E in
/-- The target plaques of radius `ε_x` lie in `closedBall x (r/2)` once `CLeaf ε_x ≤ r/2`, so the
net of `net_approx` covers them (OTL remark after the net lemma: "the compact localization
must contain the target plaques"). Blueprint node `geo:net-approx`. -/
theorem Wloc_subset_closedBall_of_small (x : X) {εx r : ℝ} (_hε : 0 < εx) (hεr : εx ≤ G.rLeaf)
    (h : G.CLeaf * εx ≤ r / 2) (k : LeafKind) :
    G.plaque k εx x ⊆ Metric.closedBall x (r / 2) := by
  intro y hy
  obtain ⟨hyW, hyd⟩ := hy
  have h1 : dist x y ≤ G.CLeaf * G.dW k x y :=
    G.dist_le_CLeaf_mul_dW k x y hyW (lt_of_lt_of_le hyd hεr)
  have hC : 0 ≤ G.CLeaf := by linarith [G.one_le_CLeaf]
  rw [Metric.mem_closedBall, dist_comm]
  calc dist x y ≤ G.CLeaf * G.dW k x y := h1
    _ ≤ G.CLeaf * εx := mul_le_mul_of_nonneg_left hyd.le hC
    _ ≤ r / 2 := h

end EffectiveGeodesicData

end Kolmogorov.PointToSet
