/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.SectionReconstruction
import KolmogorovMathlib.PointToSet.EffectiveLocalization.Charging

/-!
# The orbit-to-location complexity estimate (geodesic blueprint, Chapter H)

The node `geo:orbit-to-location` (OTL `lem:thmorbitconversion`) of
`geodesic_upper_bound_blueprint.md`, with the time-encoding bound and the specialization to
convergent Lyapunov averages (OTL `cor:lyapunov_specialization`).

The estimate reads, for every oracle `A` above the base oracle `B`, every regular `x` with its
fixed localization data, and all integer durations with regular endpoints
`φ Tp x ∈ Pp`, `φ (-Tm) x ∈ Pm`:
```
K^A_{C · 𝓡_ρ(x;Tp,Tm)}(z) ≤ K^A_{Tp+1}(x, f, ε) + K^A_{Tm+1}(x, f⁻¹, ε) + K^A(Tp, Tm) + O(1),
𝓡_ρ(x;Tp,Tm) = max (E₊(ρ), E₋(ρ)) = 2 ^ (-min (S_Tp u⁺(x) - ρ Tp, S_Tm u⁻(x) - ρ Tm)),
```
where `z = (box j).proj x = φ t₀ x` is the section point, `K^A_δ(z) = precisionComplexityNat`,
`K^A_n(x,T,ε) = orbitComplexityNat` and `K^A(Tp,Tm) = oraclePairComplexity`. The proof is the
composition of three shortest programs (the two orbit realizers and the pair of durations) with
the fixed decoder of `section_reconstruction`, charged by the library's
`oracle_tuple_bounds_composition`; the localization code is built into the decoder and costs a
constant depending on `x` but not on the durations (decision D7). The time term is bounded by
`2 log₂(Tp+1) + 2 log₂(Tm+1) + O(1)` through `oracle_tuple_bounds_overhead`, which is
`o(Tp + Tm)`; OTL's remark that prefix-free coding does not justify `log Tp + log Tm + O(1)`
is respected by keeping the exact pair complexity in the main statement.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-- The combined scale `𝓡_ρ(x; Tp, Tm) = max (E₊(ρ), E₋(ρ))`.
Blueprint node `geo:orbit-to-location` (OTL `eq:combined-scale`). -/
noncomputable def combinedScale (ρ : ℝ) (Tp Tm : ℕ) (x : X) : ℝ :=
  max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x)

/-- The combined scale is positive. -/
theorem combinedScale_pos (ρ : ℝ) (Tp Tm : ℕ) (x : X) : 0 < G.combinedScale ρ Tp Tm x := by
  exact lt_max_of_lt_left (G.scalePlus_pos ρ Tp x)

/-- The combined scale as one exponential. Blueprint node `geo:orbit-to-location`. -/
theorem combinedScale_eq (ρ : ℝ) (Tp Tm : ℕ) (x : X) :
    G.combinedScale ρ Tp Tm x =
      (2 : ℝ) ^ (-min (birkhoffSum G.f G.uPlus Tp x - ρ * Tp)
        (birkhoffSum G.finv G.uMinus Tm x - ρ * Tm)) := by
  exact EffectiveGeodesicData.max_scale_eq ρ Tp Tm x

/-- Its binary logarithm is minus the minimum of the two slack-adjusted accumulated rates. -/
theorem logb_combinedScale (ρ : ℝ) (Tp Tm : ℕ) (x : X) :
    Real.logb 2 (G.combinedScale ρ Tp Tm x) =
      -min (birkhoffSum G.f G.uPlus Tp x - ρ * Tp) (birkhoffSum G.finv G.uMinus Tm x - ρ * Tm) := by
  rw [G.combinedScale_eq, Real.logb_rpow (by norm_num) (by norm_num)]

end GeodesicReconstructionData

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### `geo:orbit-to-location` -/

/-- Orbit-to-location conversion (OTL `lem:thmorbitconversion`). For compact regular endpoint
sets and a rational loss `ρ` there are a plaque threshold `ε₀` and a compact neighborhood `Q` of
the endpoint sets such that, when the compact plaques over `Q` are `ε₀`-small: for every oracle
`A` above `B` and every regular `x` there are a time shift `t₀` with `|t₀| ≤ aMax` (so that
`z = φ t₀ x` is the shifted section point of the localization of `x`), a tolerance `ε`, a
constant `C > 1` and a constant `c₀` with
```
K^A_{C 𝓡_ρ(x;Tp,Tm)}(z) ≤ K^A_{Tp+1}(x,f,ε) + K^A_{Tm+1}(x,f⁻¹,ε) + K^A(Tp,Tm) + c₀
```
for all `Tp, Tm` with `φ Tp x ∈ Pp` and `φ (-Tm) x ∈ Pm`. Here `t₀`, `ε`, `C`, `c₀` do not
depend on the durations (but `t₀` depends on `Pp, Pm, ρ` through the target plaque radius).
Proof: take the decoder of `section_reconstruction` with the localization `(j, s, c, rV, r)`
built in; feed it the realizers of the two orbit complexities (packaged as orbit data by
`OrbitDatum.ofMem`) and the pair of durations; its output `q` satisfies
`dist (ι q) z ≤ C₃ 𝓡_ρ < C 𝓡_ρ` with `C = C₃ + 1`, so `precisionComplexity_le_of_program` gives
the bound;
`z = φ s (proj (φ (-s) x)) = φ t₀ x` with `t₀ = τ (φ (-s) x)`, bounded by `abs_τ_le_aMax`.
Blueprint node `geo:orbit-to-location`. -/
theorem orbit_to_location {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) (ρ : ℚ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧ Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      (G.SmallPlaques Q ε₀ →
        ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
        ∀ x ∈ G.Reg, ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 < C ∧
          ∃ c₀ : ℕ, ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
            precisionComplexityNat P A (G.φ t₀ x) (C * G.combinedScale ρ Tp Tm x) ≤
              orbitComplexityNat P G.f A x (Tp + 1) ε +
                orbitComplexityNat P G.finv A x (Tm + 1) ε +
                oraclePairComplexity A Tp Tm + c₀) := by
  obtain ⟨-, -, ε₀, hε₀, Q, hQ, hPQ, hQR, -⟩ :=
    E.section_reconstruction hPp hPpR hPm hPmR (Px := ∅) isCompact_empty (Set.empty_subset _) ρ hρ
  refine ⟨ε₀, hε₀, Q, hQ, hPQ, hQR, fun _ A hBA x hx ↦ ?_⟩
  obtain ⟨ε, hε, ε₀', hε₀', Q', hQ', -, -, recon, hrecon, hspec⟩ :=
    E.section_reconstruction hPp hPpR hPm hPmR (Px := {x}) isCompact_singleton
      (Set.singleton_subset_iff.mpr hx) ρ hρ
  obtain ⟨j, s, c, rV, r, C₃, hxj, hr, hC₃, hmain⟩ :=
    hspec (G.smallPlaques Q' ε₀') x (Set.mem_singleton x)
  -- the shifted section point is the time shift `φ t₀ x`, `t₀ = τ (φ (-s) x)`
  have hz : G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x)) =
      G.φ ((G.box j).τ (G.φ (-(s : ℝ)) x)) x := by
    unfold FlowBox.proj
    rw [← Flow.map_add, ← Flow.map_add]
    congr 1
    ring
  have ht₀ : |(G.box j).τ (G.φ (-(s : ℝ)) x)| ≤ G.aMax := G.abs_τ_le_aMax hxj
  have hε' : 0 < min ε (r / 8) := lt_min hε (by positivity)
  refine ⟨_, ht₀, min ε (r / 8), hε', C₃ + 1, by linarith, ?_⟩
  let F : ℕ × ℕ × ℕ × ℕ →. ℕ := fun d ↦
    recon (j, s, c, rV, d.1, d.2.1, d.2.2.1, d.2.2.2, r)
  have hF : PartrecIn {charOracle A} F := by
    have hg : Computable fun d : ℕ × ℕ × ℕ × ℕ ↦
        (j, s, c, rV, d.1, d.2.1, d.2.2.1, d.2.2.2, r) :=
      (Computable.const j).pair ((Computable.const s).pair ((Computable.const c).pair
        ((Computable.const rV).pair (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
          ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
            ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair
              (Computable.const r))))))))
    exact (partrecIn_mono A hBA hrecon).comp hg.computableIn
  obtain ⟨c₀, hc₀⟩ := precisionComplexity_le_of_program P A F hF
  refine ⟨c₀, fun Tp Tm hTp hTm ↦ ?_⟩
  obtain ⟨ip, hip, hKp⟩ :=
    orbitComplexityNat_attained P G.f A x G.continuous_f (Tp + 1) hε'
  obtain ⟨im, him, hKm⟩ :=
    orbitComplexityNat_attained P G.finv A x G.continuous_finv (Tm + 1) hε'
  obtain ⟨hdom, hout⟩ := hmain Tp Tm hTp hTm (OrbitDatum.ofMem hip) (OrbitDatum.ofMem him)
    rfl le_rfl rfl le_rfl
  simp only [OrbitDatum.ofMem_idx] at hdom hout
  -- every output of the program on the shortest descriptions is within `C 𝓡_ρ` of `z`
  have hlt : ∀ q ∈ F (ip, im, Tp, Tm),
      dist (P.ι q) (G.φ ((G.box j).τ (G.φ (-(s : ℝ)) x)) x) <
        (C₃ + 1) * G.combinedScale ρ Tp Tm x := by
    intro q hq
    have hdist := hout q hq
    rw [hz] at hdist
    have hpos := G.combinedScale_pos ρ Tp Tm x
    calc dist _ _ ≤ C₃ * max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) := hdist
      _ = C₃ * G.combinedScale ρ Tp Tm x := rfl
      _ < (C₃ + 1) * G.combinedScale ρ Tp Tm x := by nlinarith
  calc precisionComplexityNat P A _ _
      ≤ oracleNatComplexity A ip + oracleNatComplexity A im + oraclePairComplexity A Tp Tm + c₀ :=
        hc₀ _ _ ip im Tp Tm hdom hlt
    _ = _ := by rw [hKp, hKm]

/-- The same with the time code bounded by logarithms:
`… + 2 log₂(Tp+1) + 2 log₂(Tm+1) + c₀`. Blueprint node `geo:orbit-to-location`
(OTL `eq:complexity-log`, with the library's coarser pair overhead). -/
theorem orbit_to_location_log {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) (ρ : ℚ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧ Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      (G.SmallPlaques Q ε₀ →
        ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
        ∀ x ∈ G.Reg, ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 < C ∧
          ∃ c₀ : ℝ, ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
            (precisionComplexityNat P A (G.φ t₀ x) (C * G.combinedScale ρ Tp Tm x) : ℝ) ≤
              orbitComplexityNat P G.f A x (Tp + 1) ε +
                orbitComplexityNat P G.finv A x (Tm + 1) ε +
                2 * Real.logb 2 ((Tp : ℝ) + 1) + 2 * Real.logb 2 ((Tm : ℝ) + 1) + c₀) := by
  obtain ⟨ε₀, hε₀, Q, hQ, hPQ, hQR, h⟩ := E.orbit_to_location hPp hPpR hPm hPmR ρ hρ
  refine ⟨ε₀, hε₀, Q, hQ, hPQ, hQR, fun hsmall A hBA x hx ↦ ?_⟩
  obtain ⟨t₀, ht₀, ε, hε, C, hC, c₀, hc₀⟩ := h hsmall A hBA x hx
  obtain ⟨c, hc⟩ := oraclePairComplexity_le_log A
  refine ⟨t₀, ht₀, ε, hε, C, hC, c₀ + c, fun Tp Tm hTp hTm ↦ ?_⟩
  have h1 : (precisionComplexityNat P A (G.φ t₀ x) (C * G.combinedScale ρ Tp Tm x) : ℝ) ≤
      ((orbitComplexityNat P G.f A x (Tp + 1) ε + orbitComplexityNat P G.finv A x (Tm + 1) ε +
        oraclePairComplexity A Tp Tm + c₀ : ℕ) : ℝ) := by
    exact_mod_cast hc₀ Tp Tm hTp hTm
  have h2 := hc Tp Tm
  push_cast at h1
  linarith

/-- Specialization to the endpoint sets `Reg^u(η)`, `Reg^s(η)` (compact and regular for
`η > 0`, Chapter B). Blueprint node `geo:orbit-to-location` ("For each fixed `η > 0`, this
applies with `P⁺ = Reg^u(η)` and `P⁻ = Reg^s(η)`"). -/
theorem orbit_to_location_regU {η : ℝ} (hη : 0 < η) (ρ : ℚ) (hρ : 0 < ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧ G.regU η ∪ G.regS η ⊆ interior Q ∧
      Q ⊆ G.Reg ∧
      (G.SmallPlaques Q ε₀ →
        ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
        ∀ x ∈ G.Reg, ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 < C ∧
          ∃ c₀ : ℕ, ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ G.regU η → G.φ (-(Tm : ℝ)) x ∈ G.regS η →
            precisionComplexityNat P A (G.φ t₀ x) (C * G.combinedScale ρ Tp Tm x) ≤
              orbitComplexityNat P G.f A x (Tp + 1) ε +
                orbitComplexityNat P G.finv A x (Tm + 1) ε +
                oraclePairComplexity A Tp Tm + c₀) := by
  exact E.orbit_to_location (G.isCompact_regU η) (G.regU_subset_Reg hη) (G.isCompact_regS η)
    (G.regS_subset_Reg hη) ρ hρ

/-! ### Specialization to convergent averages (OTL `cor:lyapunov_specialization`) -/

omit E in
/-- If both average rates converge to `α > 0` (in bits), then for `0 < ρ < α` and durations
beyond a threshold the combined scale at loss `ρ/2` is at most `2 ^ (-min (Tp, Tm) (α - ρ))`.
Blueprint node `geo:orbit-to-location` (specialization). -/
theorem combinedScale_le_of_tendsto {x : X} {α : ℝ} (_hα : 0 < α)
    (hu : Tendsto (fun n : ℕ ↦ birkhoffSum G.f G.uPlus n x / n) atTop (𝓝 α))
    (hs : Tendsto (fun n : ℕ ↦ birkhoffSum G.finv G.uMinus n x / n) atTop (𝓝 α))
    {ρ : ℝ} (hρ : 0 < ρ) (hρα : ρ < α) :
    ∃ T₀ : ℕ, ∀ Tp Tm : ℕ, T₀ ≤ Tp → T₀ ≤ Tm →
      G.combinedScale (ρ / 2) Tp Tm x ≤ (2 : ℝ) ^ (-((min Tp Tm : ℕ) : ℝ) * (α - ρ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hu.eventually (eventually_ge_nhds (by linarith : α - ρ / 2 < α)))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hs.eventually (eventually_ge_nhds (by linarith : α - ρ / 2 < α)))
  refine ⟨max (max N₁ N₂) 1, fun Tp Tm hTp hTm ↦ ?_⟩
  have hαρ : 0 ≤ α - ρ := by linarith
  have hmin : ((min Tp Tm : ℕ) : ℝ) ≤ Tp := by exact_mod_cast min_le_left Tp Tm
  have hmin' : ((min Tp Tm : ℕ) : ℝ) ≤ Tm := by exact_mod_cast min_le_right Tp Tm
  have hTp1 : (1 : ℝ) ≤ Tp := by exact_mod_cast le_trans (le_max_right _ _) hTp
  have hTm1 : (1 : ℝ) ≤ Tm := by exact_mod_cast le_trans (le_max_right _ _) hTm
  have e1 := hN₁ Tp (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTp)
  have e2 := hN₂ Tm (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTm)
  rw [le_div_iff₀ (by linarith)] at e1 e2
  have m1 := mul_le_mul_of_nonneg_left hmin hαρ
  have m2 := mul_le_mul_of_nonneg_left hmin' hαρ
  unfold GeodesicReconstructionData.combinedScale GeodesicReconstructionData.scalePlus
    GeodesicReconstructionData.scaleMinus
  apply max_le
  · apply Real.rpow_le_rpow_of_exponent_le one_le_two
    nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le one_le_two
    nlinarith

/-- The orbit-to-location estimate at the Lyapunov scale `C 2 ^ (-min (Tp, Tm) (α - ρ))` for
points whose forward unstable and backward stable averages converge to `α > 0`
(MAIN `lem:thmorbitconversion` in its original `α - ρ` form). Uses `orbit_to_location` at loss
`ρ/2` and antitonicity of precision complexity in the radius.
Blueprint node `geo:orbit-to-location` (specialization). -/
theorem orbit_to_location_lyapunov {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {α : ℝ} (hα : 0 < α) (ρ : ℚ) (hρ : 0 < ρ)
    (hρα : (ρ : ℝ) < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧ Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      (G.SmallPlaques Q ε₀ →
        ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A →
        ∀ x ∈ G.Reg,
          Tendsto (fun n : ℕ ↦ birkhoffSum G.f G.uPlus n x / n) atTop (𝓝 α) →
          Tendsto (fun n : ℕ ↦ birkhoffSum G.finv G.uMinus n x / n) atTop (𝓝 α) →
          ∃ t₀ : ℝ, |t₀| ≤ G.aMax ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 1 < C ∧
          ∃ c₀ T₀ : ℕ, ∀ Tp Tm : ℕ, T₀ ≤ Tp → T₀ ≤ Tm →
            G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
            precisionComplexityNat P A (G.φ t₀ x)
                (C * (2 : ℝ) ^ (-((min Tp Tm : ℕ) : ℝ) * (α - ρ))) ≤
              orbitComplexityNat P G.f A x (Tp + 1) ε +
                orbitComplexityNat P G.finv A x (Tm + 1) ε +
                oraclePairComplexity A Tp Tm + c₀) := by
  obtain ⟨ε₀, hε₀, Q, hQ, hPQ, hQR, h⟩ :=
    E.orbit_to_location hPp hPpR hPm hPmR (ρ / 2) (by positivity)
  refine ⟨ε₀, hε₀, Q, hQ, hPQ, hQR, fun hsmall A hBA x hx hu hs ↦ ?_⟩
  obtain ⟨t₀, ht₀, ε, hε, C, hC, c₀, hc₀⟩ := h hsmall A hBA x hx
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  obtain ⟨T₀, hT₀⟩ := combinedScale_le_of_tendsto (G := G) hα hu hs hρ' hρα
  refine ⟨t₀, ht₀, ε, hε, C, hC, c₀, T₀, fun Tp Tm hTp hTm hPp' hPm' ↦ ?_⟩
  have hb := hc₀ Tp Tm hPp' hPm'
  have hcs : G.combinedScale ((ρ / 2 : ℚ) : ℝ) Tp Tm x = G.combinedScale ((ρ : ℝ) / 2) Tp Tm x := by
    push_cast
    rfl
  have hle := hT₀ Tp Tm hTp hTm
  have hpos := G.combinedScale_pos ((ρ / 2 : ℚ) : ℝ) Tp Tm x
  refine le_trans (precisionComplexityNat_anti P A (by positivity) ?_) hb
  rw [hcs]
  exact mul_le_mul_of_nonneg_left hle (by linarith)

end EffectiveGeodesicData

end Kolmogorov.PointToSet
