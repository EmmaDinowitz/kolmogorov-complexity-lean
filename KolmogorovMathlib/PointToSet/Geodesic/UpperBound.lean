/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.Mixed
import KolmogorovMathlib.PointToSet.BSDimension.Upper
import KolmogorovMathlib.PointToSet.Conformal.Classical

/-!
# From the estimate to the dimension bound (geodesic blueprint, Chapter I)

The main theorems `geo:main-pointwise` and `geo:main-set` of `geodesic_upper_bound_blueprint.md`,
the "controlled-return upper bound" of PO §4.2, steps 5–6. The chapter is split along its
topics:

* `UpperBound/Returns.lean`: `ControlledReturns`, `PositiveRates`, stopping times and the
  return adjustment (`geo:controlled-returns`, `geo:positive-rates`, `geo:stopping-times`,
  `geo:return-adjustment`);
* `UpperBound/PrecisionChain.lean`: the interface `OrbitToLocationEstimate` to Chapter H and the
  precision chain (`geo:precision-chain`), with the `ℝ≥0∞` limit helpers;
* `UpperBound/SectionPoint.lean`: the flow coordinate and the upper section-point bound
  (`geo:flow-coordinate`, `geo:section-point-upper`);
* `UpperBound/Mixed.lean`: the mixed section-point bound (`geo:section-point-mixed`);
* this file: `main_pointwise` and `main_set`.

## The interface

Chapter H proves the orbit-to-location estimate under the side condition `SmallPlaques Q ε₀`
for a compact `Q` and a threshold `ε₀` that it produces. The limit arguments of this chapter
only use the conclusion, so they are stated for an oracle `A` satisfying the predicate
`OrbitToLocationEstimate G P A`. The section point depends on the endpoint sets and the loss;
the flow-coordinate step `flow_coordinate` (`Dim x ≤ 1 + Dim (φ t₀ x)`) is therefore applied
inside the parameter loop, before the limits (PO: "keep `D`, `U`, `t₀` fixed as precision
increases" is replaced by "restore the flow coordinate at every stage").

## Conventions

`dim^A(x), Dim^A(x) = (staticPointDimensions P A x).1, .2`;
`dim^A_BS, Dim^A_BS = (pointwiseBSDimension P T u A x).1, .2` for `(T, u) = (f, u⁺)` forward
and `(f⁻¹, u⁻)` backward. All dimensions are `ℝ≥0∞`. Integer return times (decision D6);
`u^± ≥ 0` (G2) is load-bearing in `return_adjustment`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### `geo:main-pointwise` -/

/-- Pointwise upper bounds (`thm:upperbounds`). For every oracle `A` above `B` satisfying the
interface, every `x ∈ 𝓡` with positive lower forward unstable and backward stable rates:
```
Dim^A(x) ≤ 1 + Dim^A_BS(x,f,u⁺) + Dim^A_BS(x,f⁻¹,u⁻)
dim^A(x) ≤ 1 + min (dim^A_BS(x,f,u⁺) + Dim^A_BS(x,f⁻¹,u⁻), Dim^A_BS(x,f,u⁺) + dim^A_BS(x,f⁻¹,u⁻))
```
`sectionPoint_upper` and `sectionPoint_mixed` (which already contain the flow-coordinate step).
✎ The stable term is the backward quantity `(f⁻¹, u⁻)`. Blueprint node `geo:main-pointwise`. -/
theorem main_pointwise {A : Set ℕ} (hBA : charOracle B ≤ᵀ charOracle A)
    (hA : OrbitToLocationEstimate G P A) {x : X} (hx : G.ControlledReturns x)
    (hpos : G.PositiveRates x) :
    (staticPointDimensions P A x).2 ≤
        1 + (pointwiseBSDimension P G.f G.uPlus A x).2 +
          (pointwiseBSDimension P G.finv G.uMinus A x).2 ∧
      (staticPointDimensions P A x).1 ≤
        1 + min ((pointwiseBSDimension P G.f G.uPlus A x).1 +
            (pointwiseBSDimension P G.finv G.uMinus A x).2)
          ((pointwiseBSDimension P G.f G.uPlus A x).2 +
            (pointwiseBSDimension P G.finv G.uMinus A x).1) := by
  exact ⟨sectionPoint_upper P E hBA hA hx hpos, sectionPoint_mixed P E hBA hA
    (E.mono hBA).presentation (E.mono hBA).f_represented (E.mono hBA).finv_represented hx hpos⟩

/-! ### `geo:main-set` -/

/-- Set-level consequence. For `Z ⊆ 𝓡` with positive rates at every point, if every oracle
above `B` satisfies the interface:
```
dim_P Z ≤ 1 + Dim_BS(Z,f,u⁺) + Dim_BS(Z,f⁻¹,u⁻)
dim_H Z ≤ 1 + min (dim_BS(Z,f,u⁺) + Dim_BS(Z,f⁻¹,u⁻), Dim_BS(Z,f,u⁺) + dim_BS(Z,f⁻¹,u⁻))
```
Proof: `bsPointToSet_cone` for `(f, u⁺, Z)` and `(f⁻¹, u⁻, Z)` (positivity is exactly the
hypothesis `hZ`), join the two cones with `B` by `oracleJoin`, restrict the classical minima to
that cone by `classicalPointToSet_cone_upper` / `classicalPointToSet_cone`, apply
`main_pointwise` at the joined oracle and take suprema (`sup_x min ≤ min sup_x`).
Blueprint node `geo:main-set`. -/
theorem main_set (hA : ∀ A : Set ℕ, charOracle B ≤ᵀ charOracle A → OrbitToLocationEstimate G P A)
    {Z : Set X} (hZR : ∀ x ∈ Z, G.ControlledReturns x) (hZ : ∀ x ∈ Z, G.PositiveRates x) :
    metricPackingDimension Z ≤
        1 + upperBSDimension G.f G.uPlus Z + upperBSDimension G.finv G.uMinus Z ∧
      _root_.dimH Z ≤
        1 + min (lowerBSDimension G.f G.uPlus Z + upperBSDimension G.finv G.uMinus Z)
          (upperBSDimension G.f G.uPlus Z + lowerBSDimension G.finv G.uMinus Z) := by
  obtain ⟨A₁, hA₁⟩ := bsPointToSet_cone P G.f G.continuous_f G.uPlus G.uPlus_props.1 Z
    fun x hx ↦ (hZ x hx).1
  obtain ⟨A₂, hA₂⟩ := bsPointToSet_cone P G.finv G.continuous_finv G.uMinus G.uMinus_props.1 Z
    fun x hx ↦ (hZ x hx).2
  have h₁ : charOracle A₁ ≤ᵀ charOracle (oracleJoin (oracleJoin A₁ A₂) B) :=
    (oracle_joins A₁ A₂).trans (oracle_joins (oracleJoin A₁ A₂) B)
  have h₂ : charOracle A₂ ≤ᵀ charOracle (oracleJoin (oracleJoin A₁ A₂) B) :=
    (oracle_joins_right A₁ A₂).trans (oracle_joins (oracleJoin A₁ A₂) B)
  have hB : charOracle B ≤ᵀ charOracle (oracleJoin (oracleJoin A₁ A₂) B) :=
    oracle_joins_right (oracleJoin A₁ A₂) B
  obtain ⟨-, hc₁⟩ := hA₁ _ h₁
  obtain ⟨-, hc₂⟩ := hA₂ _ h₂
  have e₁ : upperBSDimension G.f G.uPlus Z =
      ⨆ x ∈ Z, (pointwiseBSDimension P G.f G.uPlus (oracleJoin (oracleJoin A₁ A₂) B) x).2 :=
    hc₁ .upper
  have e₂ : lowerBSDimension G.f G.uPlus Z =
      ⨆ x ∈ Z, (pointwiseBSDimension P G.f G.uPlus (oracleJoin (oracleJoin A₁ A₂) B) x).1 :=
    hc₁ .lower
  have e₃ : upperBSDimension G.finv G.uMinus Z =
      ⨆ x ∈ Z, (pointwiseBSDimension P G.finv G.uMinus (oracleJoin (oracleJoin A₁ A₂) B) x).2 :=
    hc₂ .upper
  have e₄ : lowerBSDimension G.finv G.uMinus Z =
      ⨆ x ∈ Z, (pointwiseBSDimension P G.finv G.uMinus (oracleJoin (oracleJoin A₁ A₂) B) x).1 :=
    hc₂ .lower
  have hpt : ∀ x ∈ Z, _ ∧ _ := fun x hx ↦ E.main_pointwise hB (hA _ hB) (hZR x hx) (hZ x hx)
  have hrefl : charOracle (oracleJoin (oracleJoin A₁ A₂) B) ≤ᵀ
      charOracle (oracleJoin (oracleJoin A₁ A₂) B) := TuringReducible.refl _
  constructor
  · have hle : (⨅ A : Set ℕ, ⨅ (_ : charOracle (oracleJoin (oracleJoin A₁ A₂) B) ≤ᵀ charOracle A),
        ⨆ x ∈ Z, (staticPointDimensions P A x).2) ≤
        ⨆ x ∈ Z, (staticPointDimensions P (oracleJoin (oracleJoin A₁ A₂) B) x).2 :=
      iInf_le_of_le (oracleJoin (oracleJoin A₁ A₂) B) (iInf_le_of_le hrefl le_rfl)
    rw [classicalPointToSet_cone_upper P Z (oracleJoin (oracleJoin A₁ A₂) B)]
    refine hle.trans (iSup₂_le fun x hx ↦ (hpt x hx).1.trans ?_)
    rw [e₁, e₃]
    gcongr <;> exact le_iSup₂_of_le x hx le_rfl
  · have hle : (⨅ A : Set ℕ, ⨅ (_ : charOracle (oracleJoin (oracleJoin A₁ A₂) B) ≤ᵀ charOracle A),
        ⨆ x ∈ Z, (staticPointDimensions P A x).1) ≤
        ⨆ x ∈ Z, (staticPointDimensions P (oracleJoin (oracleJoin A₁ A₂) B) x).1 :=
      iInf_le_of_le (oracleJoin (oracleJoin A₁ A₂) B) (iInf_le_of_le hrefl le_rfl)
    rw [classicalPointToSet_cone P Z (oracleJoin (oracleJoin A₁ A₂) B)]
    refine hle.trans (iSup₂_le fun x hx ↦ (hpt x hx).2.trans ?_)
    rw [e₁, e₂, e₃, e₄]
    gcongr <;> exact le_iSup₂_of_le x hx le_rfl

omit E in
/-- The hypotheses of the library's `bsPointToSet_cone` hold for the forward data on a set with
positive rates: `f` is continuous, `u⁺` is uniformly continuous, and the lower average is
positive at every point. Blueprint node `geo:main-set`. -/
theorem bsPointToSet_cone_forward {Z : Set X} (hZ : ∀ x ∈ Z, G.PositiveRates x) :
    ∃ A₀ : Set ℕ, ∀ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A →
      IsAdmissible P G.f (fun _ : Fin 1 ↦ G.uPlus) A ∧ ∀ σ : LimitSide,
        σ.choose (lowerBSDimension G.f G.uPlus Z, upperBSDimension G.f G.uPlus Z) =
          ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P G.f G.uPlus A x) := by
  exact bsPointToSet_cone P G.f G.continuous_f G.uPlus G.uPlus_props.1 Z
    fun x hx ↦ (hZ x hx).1

omit E in
/-- Backward counterpart. Blueprint node `geo:main-set`. -/
theorem bsPointToSet_cone_backward {Z : Set X} (hZ : ∀ x ∈ Z, G.PositiveRates x) :
    ∃ A₀ : Set ℕ, ∀ A : Set ℕ, charOracle A₀ ≤ᵀ charOracle A →
      IsAdmissible P G.finv (fun _ : Fin 1 ↦ G.uMinus) A ∧ ∀ σ : LimitSide,
        σ.choose (lowerBSDimension G.finv G.uMinus Z, upperBSDimension G.finv G.uMinus Z) =
          ⨆ x ∈ Z, σ.choose (pointwiseBSDimension P G.finv G.uMinus A x) := by
  exact bsPointToSet_cone P G.finv G.continuous_finv G.uMinus G.uMinus_props.1 Z
    fun x hx ↦ (hZ x hx).2

end EffectiveGeodesicData

end Kolmogorov.PointToSet
