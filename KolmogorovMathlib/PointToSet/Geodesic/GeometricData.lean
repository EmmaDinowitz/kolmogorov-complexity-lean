/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface

/-!
# Geometric standing data (geodesic blueprint, Chapter B)

The nodes `geo:geometric-data`, `geo:lps-from-compact`,
`geo:plaque-expansivity` and `geo:leafwise-contraction` of
`geodesic_upper_bound_blueprint.md`.

Mathlib has no geodesic flows, Jacobi fields, horospheres or invariant foliations. Following
blueprint decision D5, the geometric facts actually used by the reconstruction argument are
collected as the fields of one structure, `GeodesicReconstructionData`, extending the
analytic `FlowData` of Chapter A. Each field is a classical fact about the geodesic flow of
a closed rank-one surface of nonpositive curvature (references in the blueprint); nothing
here is specific to that setting beyond the fields themselves, so the structure can be
instantiated by any flow with the same local hyperbolic structure.

Conventions. `Reg := Singᶜ`. Four leaf kinds `u, s, cu, cs` carry leaves `W k x`, leaf
pseudometrics `dW k x y` (meaningful on a common leaf) and plaques
`plaque k r x = {y ∈ W k x | dW k x y < r}`; `Wloc k x` is the plaque of the fixed leaf
radius `rLeaf`. The two local products are `bracketS v w = [v,w]_s ∈ W u v ∩ W cs w` and
`bracketU v w = [v,w]_u ∈ W cu v ∩ W s w`. The transverse estimate (G11) is stated with the
ambient distance on the section, which is all the reconstruction uses, so no intrinsic
section metric is introduced.

Leafwise contraction (G5) and the transverse estimate (G11) are fields, not theorems: their
proofs in the drafts use Jacobi fields and the inverse function theorem in a chart, and the
blueprint proposes taking the consequences as hypotheses in a first pass.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The four kinds of invariant leaves: strong unstable, strong stable, center unstable and
center stable. Blueprint node `geo:geometric-data` (G3). -/
inductive LeafKind where
  /-- Strong unstable leaves `W^u`. -/
  | u
  /-- Strong stable leaves `W^s`. -/
  | s
  /-- Center unstable leaves `W^{cu}`. -/
  | cu
  /-- Center stable leaves `W^{cs}`. -/
  | cs
  deriving DecidableEq

/-- A flow box: an open set `U` with a transverse section `D ⊆ U`, a local time `τ` and the
section projection `Π y = φ (τ y) y`, the local time being the unique one in `(-a, a)` that
lands on `D`. Blueprint node `geo:geometric-data` (G12). -/
structure FlowBox (φ : Flow ℝ X) where
  /-- The open domain of the box. -/
  U : Set X
  /-- The domain is open. -/
  isOpen_U : IsOpen U
  /-- The section. -/
  D : Set X
  /-- The section lies in the domain. -/
  D_subset : D ⊆ U
  /-- The section is nonempty (a degenerate empty box is excluded; needed so that a dense
  computable sequence on the section exists, `exists_effectiveGeodesicData`). -/
  D_nonempty : D.Nonempty
  /-- Half-width of the time interval. -/
  a : ℝ
  /-- The time interval is nondegenerate. -/
  a_pos : 0 < a
  /-- The local time to the section. -/
  τ : X → ℝ
  /-- The local time is continuous on the domain. -/
  continuousOn_τ : ContinuousOn τ U
  /-- The local time is small. -/
  abs_τ_lt : ∀ y ∈ U, |τ y| < a
  /-- Flowing by the local time lands on the section. -/
  flow_τ_mem : ∀ y ∈ U, φ (τ y) y ∈ D
  /-- The local time is the unique time in `(-a, a)` landing on the section. -/
  τ_unique : ∀ y ∈ U, ∀ t : ℝ, |t| < a → φ t y ∈ D → t = τ y

/-- The section projection of a flow box. Blueprint node `geo:geometric-data` (G12). -/
def FlowBox.proj {φ : Flow ℝ X} (b : FlowBox φ) (y : X) : X := φ (b.τ y) y

/-- Geometric standing data for the reconstruction argument: a flow with singular set, rate
functions, four invariant leaf families with leaf pseudometrics, nonexpansion and leafwise
contraction, center-leg control, local product structure near compact regular sets with
branch consistency, expansivity on the regular set, compact plaques at every point,
the transverse estimate on sections, and a finite atlas of flow boxes. Blueprint node
`geo:geometric-data` (fields G1–G12). -/
structure GeodesicReconstructionData (X : Type*) [MetricSpace X] [CompactSpace X]
    extends FlowData X where
  /-- (G1) The singular set. -/
  Sing : Set X
  /-- (G1) The singular set is closed. -/
  isClosed_Sing : IsClosed Sing
  /-- (G1) The singular set is flow invariant. -/
  Sing_invariant : ∀ t : ℝ, φ t '' Sing = Sing
  /-- (G2) The unstable rate. -/
  lamU : X → ℝ
  /-- (G2) The stable rate. -/
  lamS : X → ℝ
  /-- (G2) The unstable rate is continuous. -/
  continuous_lamU : Continuous lamU
  /-- (G2) The stable rate is continuous. -/
  continuous_lamS : Continuous lamS
  /-- (G2) A common upper bound of the rates. -/
  Λ : ℝ
  /-- (G2) Rates are nonnegative (nonpositive curvature); load-bearing in Chapter I. -/
  lamU_nonneg : ∀ x, 0 ≤ lamU x
  /-- (G2) Rates are nonnegative (nonpositive curvature). -/
  lamS_nonneg : ∀ x, 0 ≤ lamS x
  /-- (G2) Rates are bounded. -/
  lamU_le : ∀ x, lamU x ≤ Λ
  /-- (G2) Rates are bounded. -/
  lamS_le : ∀ x, lamS x ≤ Λ
  /-- (G2) Both rates vanish exactly on the singular set. -/
  lam_eq_zero_iff : ∀ x, (lamU x = 0 ∧ lamS x = 0) ↔ x ∈ Sing
  /-- (G3) The leaves of the four kinds. -/
  W : LeafKind → X → Set X
  /-- (G3) The leaf pseudometrics, meaningful on a common leaf. -/
  dW : LeafKind → X → X → ℝ
  /-- (G3) Every point lies on its own leaves. -/
  mem_W : ∀ k x, x ∈ W k x
  /-- (G3) Leaves form a partition: a point of a leaf has the same leaf. -/
  W_eq_of_mem : ∀ k x y, y ∈ W k x → W k y = W k x
  /-- (G3) The leaf pseudometric vanishes on the diagonal. -/
  dW_self : ∀ k x, dW k x x = 0
  /-- (G3) The leaf pseudometric is symmetric. -/
  dW_comm : ∀ k x y, dW k x y = dW k y x
  /-- (G3) The leaf pseudometric satisfies the triangle inequality on a common leaf. -/
  dW_triangle : ∀ k x y z, y ∈ W k x → z ∈ W k x → dW k x z ≤ dW k x y + dW k y z
  /-- (G3) Leaves are flow invariant. -/
  W_invariant : ∀ k (t : ℝ) x, φ t '' W k x = W k (φ t x)
  /-- (G3) Center stable leaves are the flow saturations of strong stable leaves. -/
  W_cs_eq : ∀ x, W .cs x = ⋃ t : ℝ, φ t '' W .s x
  /-- (G3) Center unstable leaves are the flow saturations of strong unstable leaves. -/
  W_cu_eq : ∀ x, W .cu x = ⋃ t : ℝ, φ t '' W .u x
  /-- (G3) The fixed radius of the local plaques. -/
  rLeaf : ℝ
  /-- (G3) The local plaque radius is positive. -/
  rLeaf_pos : 0 < rLeaf
  /-- (G3) Leaf-to-ambient comparison constant on local plaques. -/
  CLeaf : ℝ
  /-- (G3) The comparison constant is at least one. -/
  one_le_CLeaf : 1 ≤ CLeaf
  /-- (G3) On local plaques the ambient distance is at most `CLeaf` times the leaf distance
  (`d_K ≤ C d^*` of OTL §1; the leaf distance is a projected curve length). -/
  dist_le_CLeaf_mul_dW : ∀ k x y, y ∈ W k x → dW k x y < rLeaf → dist x y ≤ CLeaf * dW k x y
  /-- (G3'') The flow line through `x` lies in both center leaves and has center-leaf length
  at most the elapsed time (unit projected speed of the geodesic flow). Added during the
  formalization: needed to place the section point in the target plaques. -/
  dW_cs_flow_self : ∀ x (t : ℝ), dW .cs x (φ t x) ≤ |t|
  /-- (G3'') Center unstable counterpart. -/
  dW_cu_flow_self : ∀ x (t : ℝ), dW .cu x (φ t x) ≤ |t|
  /-- (G4) Forward nonexpansion of the strong stable leaf distance. -/
  dW_s_flow_le : ∀ x y, y ∈ W .s x → ∀ t : ℝ, 0 ≤ t → dW .s (φ t x) (φ t y) ≤ dW .s x y
  /-- (G4) Backward nonexpansion of the strong unstable leaf distance. -/
  dW_u_flow_le : ∀ x y, y ∈ W .u x → ∀ t : ℝ, 0 ≤ t →
    dW .u (φ (-t) x) (φ (-t) y) ≤ dW .u x y
  /-- (G5) Leafwise stable contraction along a reference orbit, with loss `β`.
  Blueprint node `geo:leafwise-contraction`. -/
  leafwise_contraction_s : ∀ β : ℝ, 0 < β → ∃ δ : ℝ, 0 < δ ∧
    ∀ (v w w' : X) (T : ℝ), 0 ≤ T → w ∈ W .s v → dW .s v w < δ → w' ∈ W .s v →
      dW .s v w' < δ →
      dW .s (φ T w) (φ T w') ≤
        dW .s w w' * Real.exp (-((∫ τ in (0 : ℝ)..T, lamS (φ τ v)) - β * T))
  /-- (G5) Leafwise unstable contraction in backward time along a reference orbit.
  Blueprint node `geo:leafwise-contraction`. -/
  leafwise_contraction_u : ∀ β : ℝ, 0 < β → ∃ δ : ℝ, 0 < δ ∧
    ∀ (v w w' : X) (T : ℝ), 0 ≤ T → w ∈ W .u v → dW .u v w < δ → w' ∈ W .u v →
      dW .u v w' < δ →
      dW .u (φ (-T) w) (φ (-T) w') ≤
        dW .u w w' * Real.exp (-((∫ τ in (0 : ℝ)..T, lamU (φ (-τ) v)) - β * T))
  /-- (G6) Center-leg control constant. -/
  Cc : ℝ
  /-- (G6) The center-leg constant is nonnegative. -/
  Cc_nonneg : 0 ≤ Cc
  /-- (G6) Short center stable legs stay uniformly short in forward time. -/
  center_leg_cs : ∀ x y, y ∈ W .cs x → dW .cs x y < rLeaf → ∀ t : ℝ, 0 ≤ t →
    dist (φ t y) (φ t x) ≤ Cc * dW .cs x y
  /-- (G6) Short center unstable legs stay uniformly short in backward time. -/
  center_leg_cu : ∀ x y, y ∈ W .cu x → dW .cu x y < rLeaf → ∀ t : ℝ, 0 ≤ t →
    dist (φ (-t) y) (φ (-t) x) ≤ Cc * dW .cu x y
  /-- (G7) The local product `[v,w]_s ∈ W^u(v) ∩ W^{cs}(w)`, a total function whose
  meaning is fixed by `lps` on close pairs near a compact regular set. -/
  bracketS : X → X → X
  /-- (G7) The local product `[v,w]_u ∈ W^{cu}(v) ∩ W^s(w)`. -/
  bracketU : X → X → X
  /-- (G7) Local product structure near every compact regular set: for pairs `δ`-close to
  a point of the set and to each other (the hypothesis is stated with a witness rather than
  with `Metric.infDist`, which vanishes on the empty set), the brackets exist in the
  `κδ`-plaques, are unique there, and
  satisfy the leg bounds `d^u(v,[v,w]_s) ≤ κ d(v,w)`, `d^{cs}(w,[v,w]_s) ≤ κ d(v,w)` and
  the symmetric ones for `[v,w]_u`. Blueprint node `geo:geometric-data` (G7) and
  `geo:lps-from-compact`. -/
  lps : ∀ Q : Set X, IsCompact Q → Q ⊆ Singᶜ → ∃ δ : ℝ, 0 < δ ∧ ∃ κ : ℝ, 1 ≤ κ ∧
    ∀ v w : X, (∃ q ∈ Q, dist v q < δ) → dist v w < δ →
      (bracketS v w ∈ W .u v ∧ dW .u v (bracketS v w) ≤ κ * dist v w ∧
        bracketS v w ∈ W .cs w ∧ dW .cs w (bracketS v w) ≤ κ * dist v w ∧
        ∀ z, z ∈ W .u v → dW .u v z < κ * δ → z ∈ W .cs w → dW .cs w z < κ * δ →
          z = bracketS v w) ∧
      (bracketU v w ∈ W .cu v ∧ dW .cu v (bracketU v w) ≤ κ * dist v w ∧
        bracketU v w ∈ W .s w ∧ dW .s w (bracketU v w) ≤ κ * dist v w ∧
        ∀ z, z ∈ W .cu v → dW .cu v z < κ * δ → z ∈ W .s w → dW .s w z < κ * δ →
          z = bracketU v w)
  /-- (G8) Branch consistency: within the local product scale of a compact regular set,
  the bracket `[p, ·]_s` is constant along center stable plaques and `[·, p]_u` along center
  unstable plaques. Blueprint node `geo:geometric-data` (G8). -/
  branch_consistency : ∀ Q : Set X, IsCompact Q → Q ⊆ Singᶜ → ∃ δ : ℝ, 0 < δ ∧
    ∀ p x y : X, (∃ q ∈ Q, dist p q < δ) → dist p x < δ → dist p y < δ →
      (y ∈ W .cs x → dW .cs x y < δ → bracketS p y = bracketS p x) ∧
      (y ∈ W .cu x → dW .cu x y < δ → bracketU y p = bracketU x p)
  /-- (G9) Expansivity radius on the regular set. -/
  rExp : ℝ
  /-- (G9) The expansivity radius is positive. -/
  rExp_pos : 0 < rExp
  /-- (G9) Expansivity at regular points (flat strip theorem): an orbit staying within
  `2 rExp` of a regular orbit for all time is a small time shift of it. -/
  expansive : ∀ z, z ∈ Singᶜ → ∀ w, (∀ t : ℝ, dist (φ t w) (φ t z) ≤ 2 * rExp) →
    ∃ s : ℝ, |s| ≤ 2 * rExp ∧ w = φ s z
  /-- (G3') Strong plaques are transverse to the flow at the expansivity scale: over a compact
  regular set there is a plaque radius such that a time shift by `|s| ≤ 2 rExp` of a point of a
  closed unstable plaque that lands in the same closed plaque is trivial. Added during the
  formalization: not derivable from the other fields (see `NOTES_B.md`). -/
  plaque_transverse_u : ∀ Q : Set X, IsCompact Q → Q ⊆ Singᶜ → ∃ ε₁ : ℝ, 0 < ε₁ ∧
    ∀ p ∈ Q, ∀ y ∈ closure {y' ∈ W .u p | dW .u p y' < ε₁}, ∀ s : ℝ, |s| ≤ 2 * rExp →
      φ s y ∈ closure {y' ∈ W .u p | dW .u p y' < ε₁} → φ s y = y
  /-- (G3') Stable counterpart, for the backward decoder. -/
  plaque_transverse_s : ∀ Q : Set X, IsCompact Q → Q ⊆ Singᶜ → ∃ ε₁ : ℝ, 0 < ε₁ ∧
    ∀ p ∈ Q, ∀ y ∈ closure {y' ∈ W .s p | dW .s p y' < ε₁}, ∀ s : ℝ, |s| ≤ 2 * rExp →
      φ s y ∈ closure {y' ∈ W .s p | dW .s p y' < ε₁} → φ s y = y
  /-- (G10) Compact unstable plaques at every point and every rational radius `r`:
  a compact set squeezed between the open plaque of radius `r/2` and the closure of the open
  plaque of radius `r`. The radius is chosen by the decoders (blueprint v2, item 8.1); a fixed
  plaque cannot be small at every scale the reconstruction requests. -/
  Kplaque : ℚ → X → Set X
  /-- (G10) Compact stable plaques, likewise. -/
  Kplaque' : ℚ → X → Set X
  /-- (G10) Squeezing property of the unstable plaques. -/
  Kplaque_spec : ∀ p : X, ∀ r : ℚ, 0 < r → IsCompact (Kplaque r p) ∧
    {y ∈ W .u p | dW .u p y < (r : ℝ) / 2} ⊆ Kplaque r p ∧
    Kplaque r p ⊆ closure {y ∈ W .u p | dW .u p y < (r : ℝ)}
  /-- (G10) Squeezing property of the stable plaques. -/
  Kplaque'_spec : ∀ p : X, ∀ r : ℚ, 0 < r → IsCompact (Kplaque' r p) ∧
    {y ∈ W .s p | dW .s p y < (r : ℝ) / 2} ⊆ Kplaque' r p ∧
    Kplaque' r p ⊆ closure {y ∈ W .s p | dW .s p y < (r : ℝ)}
  /-- (G12) The number of flow boxes. -/
  nBoxes : ℕ
  /-- (G12) The flow boxes. -/
  box : Fin nBoxes → FlowBox φ
  /-- (G12) Smaller boxes with compact closures inside the domains. -/
  innerBox : Fin nBoxes → Set X
  /-- (G12) The inner boxes are open. -/
  isOpen_innerBox : ∀ j, IsOpen (innerBox j)
  /-- (G12) The inner boxes have closure inside the box domain. -/
  closure_innerBox_subset : ∀ j, closure (innerBox j) ⊆ (box j).U
  /-- (G12) The inner boxes cover the space. -/
  innerBox_cover : ⋃ j, innerBox j = univ
  /-- (G11) Transverse estimate on a shifted section at a regular point: for a box `j`, a time
  shift `s` with `φ (-s) x` in the box, and `z = φ s (proj (φ (-s) x))` the point of the shifted
  section `φ s '' D_j` on the orbit of `x`, points of the shifted section near `z` are within a
  constant times their maximal distance to the two local center plaques of `x`. The shift lets
  the localization data place `z` inside the small target plaques (blueprint v2, item 8.1b);
  `s = 0` is the unshifted estimate `transverse_estimate_zero`.
  Blueprint nodes `geo:geometric-data` (G11) and `geo:transverse-estimate`. -/
  transverse_estimate : ∀ x, x ∈ Singᶜ → ∀ j, ∀ s : ℝ, φ (-s) x ∈ (box j).U →
    ∃ V : Set X, IsOpen V ∧ φ s ((box j).proj (φ (-s) x)) ∈ V ∧ ∃ Ltr : ℝ, 0 < Ltr ∧
      ∀ y ∈ φ s '' (box j).D ∩ V,
        dist y (φ s ((box j).proj (φ (-s) x))) ≤
          Ltr * max (Metric.infDist y {y' ∈ W .cs x | dW .cs x y' < rLeaf})
            (Metric.infDist y {y' ∈ W .cu x | dW .cu x y' < rLeaf})

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-- The regular set. Blueprint node `geo:geometric-data` (G1). -/
def Reg : Set X := G.Singᶜ

/-- The plaque of radius `r` of kind `k` about `x`. Blueprint node `geo:geometric-data`. -/
def plaque (k : LeafKind) (r : ℝ) (x : X) : Set X := {y ∈ G.W k x | G.dW k x y < r}

/-- The local plaque, at the fixed leaf radius. Blueprint node `geo:geometric-data`. -/
def Wloc (k : LeafKind) (x : X) : Set X := G.plaque k G.rLeaf x

/-- The compact regular set `Reg^u(η) = {λᵘ ≥ η}`. Blueprint node `geo:lps-from-compact`. -/
def regU (η : ℝ) : Set X := {x | η ≤ G.lamU x}

/-- The compact regular set `Reg^s(η) = {λˢ ≥ η}`. Blueprint node `geo:lps-from-compact`. -/
def regS (η : ℝ) : Set X := {x | η ≤ G.lamS x}

/-- The forward unit potential `u⁺` of the data, in bits. Blueprint node `geo:unit-potentials`. -/
noncomputable def uPlus : X → ℝ := G.toFlowData.unitPotential G.lamU

/-- The backward unit potential `u⁻` of the data, in bits.
Blueprint node `geo:unit-potentials`. -/
noncomputable def uMinus : X → ℝ := G.toFlowData.unitPotentialBackward G.lamS

/-! ### Elementary consequences of G1–G3 -/

/-- The regular set is open. -/
theorem isOpen_Reg : IsOpen G.Reg := by
  exact G.isClosed_Sing.isOpen_compl

/-- The regular set is flow invariant. -/
theorem Reg_invariant (t : ℝ) : G.φ t '' G.Reg = G.Reg := by
  have hb : Function.Bijective (G.φ t) := (G.φ.toHomeomorph t).bijective
  rw [Reg, Set.image_compl_eq hb, G.Sing_invariant t]

/-- A point is regular when one of its rates is positive. -/
theorem mem_Reg_of_lamU_pos {x : X} (hx : 0 < G.lamU x) : x ∈ G.Reg := by
  intro hx'
  exact hx.ne' ((G.lam_eq_zero_iff x).mpr hx').1

/-- A point is regular when one of its rates is positive. -/
theorem mem_Reg_of_lamS_pos {x : X} (hx : 0 < G.lamS x) : x ∈ G.Reg := by
  intro hx'
  exact hx.ne' ((G.lam_eq_zero_iff x).mpr hx').2

/-- `Reg^u(η)` is compact for every `η`. Blueprint node `geo:lps-from-compact`. -/
theorem isCompact_regU (η : ℝ) : IsCompact (G.regU η) := by
  exact (isClosed_le continuous_const G.continuous_lamU).isCompact

/-- `Reg^u(η)` is regular for positive `η`. Blueprint node `geo:lps-from-compact`. -/
theorem regU_subset_Reg {η : ℝ} (hη : 0 < η) : G.regU η ⊆ G.Reg := by
  exact fun x hx => G.mem_Reg_of_lamU_pos (lt_of_lt_of_le hη hx)

/-- `Reg^s(η)` is compact for every `η`. Blueprint node `geo:lps-from-compact`. -/
theorem isCompact_regS (η : ℝ) : IsCompact (G.regS η) := by
  exact (isClosed_le continuous_const G.continuous_lamS).isCompact

/-- `Reg^s(η)` is regular for positive `η`. Blueprint node `geo:lps-from-compact`. -/
theorem regS_subset_Reg {η : ℝ} (hη : 0 < η) : G.regS η ⊆ G.Reg := by
  exact fun x hx => G.mem_Reg_of_lamS_pos (lt_of_lt_of_le hη hx)

/-- The rates are uniformly continuous (compactness). -/
theorem uniformContinuous_lamU : UniformContinuous G.lamU := by
  exact CompactSpace.uniformContinuous_of_continuous G.continuous_lamU

/-- The rates are uniformly continuous (compactness). -/
theorem uniformContinuous_lamS : UniformContinuous G.lamS := by
  exact CompactSpace.uniformContinuous_of_continuous G.continuous_lamS

/-- The forward unit potential is uniformly continuous, nonnegative and bounded. -/
theorem uPlus_props :
    UniformContinuous G.uPlus ∧ (∀ x, 0 ≤ G.uPlus x) ∧ ∀ x, G.uPlus x ≤ G.Λ / Real.log 2 := by
  exact ⟨G.toFlowData.uniformContinuous_unitPotential G.continuous_lamU,
    fun x => G.toFlowData.unitPotential_nonneg G.lamU_nonneg x,
    fun x => G.toFlowData.unitPotential_le G.continuous_lamU G.lamU_le x⟩

/-- The backward unit potential is uniformly continuous, nonnegative and bounded. -/
theorem uMinus_props :
    UniformContinuous G.uMinus ∧ (∀ x, 0 ≤ G.uMinus x) ∧
      ∀ x, G.uMinus x ≤ G.Λ / Real.log 2 := by
  exact ⟨G.toFlowData.uniformContinuous_unitPotentialBackward G.continuous_lamS,
    fun x => G.toFlowData.unitPotentialBackward_nonneg G.lamS_nonneg x,
    fun x => G.toFlowData.unitPotentialBackward_le G.continuous_lamS G.lamS_le x⟩

/-- Plaques are flow equivariant up to the leaf metric; here only the leaf statement:
the image of a leaf is the leaf of the image. -/
theorem mem_W_flow {k : LeafKind} {x y : X} (hy : y ∈ G.W k x) (t : ℝ) :
    G.φ t y ∈ G.W k (G.φ t x) := by
  rw [← G.W_invariant k t x]
  exact Set.mem_image_of_mem _ hy

/-- Points of a local plaque are within `CLeaf * dW` of the center in the ambient metric,
hence within `CLeaf * rLeaf`. -/
theorem dist_lt_of_mem_Wloc {k : LeafKind} {x y : X} (hy : y ∈ G.Wloc k x) :
    dist x y < G.CLeaf * G.rLeaf := by
  obtain ⟨hyW, hyd⟩ := hy
  calc dist x y ≤ G.CLeaf * G.dW k x y := G.dist_le_CLeaf_mul_dW k x y hyW hyd
    _ < G.CLeaf * G.rLeaf :=
      mul_lt_mul_of_pos_left hyd (lt_of_lt_of_le one_pos G.one_le_CLeaf)

/-! ### `geo:lps-from-compact`: local product structure near `Reg^u(η)`, `Reg^s(η)` -/

/-- Specialization of the local product field to the compact regular sets `Reg^u(η)` and
`Reg^s(η)`. Blueprint node `geo:lps-from-compact`. -/
theorem exists_lps_regU {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∃ κ : ℝ, 1 ≤ κ ∧
    ∀ v w : X, (∃ q ∈ G.regU η, dist v q < δ) → dist v w < δ →
      G.bracketS v w ∈ G.W .u v ∧ G.dW .u v (G.bracketS v w) ≤ κ * dist v w ∧
        G.bracketS v w ∈ G.W .cs w ∧ G.dW .cs w (G.bracketS v w) ≤ κ * dist v w := by
  obtain ⟨δ, hδ, κ, hκ, h⟩ := G.lps (G.regU η) (G.isCompact_regU η) (G.regU_subset_Reg hη)
  refine ⟨δ, hδ, κ, hκ, fun v w hv hvw => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := (h v w hv hvw).1
  exact ⟨h1, h2, h3, h4⟩

/-- Backward specialization. Blueprint node `geo:lps-from-compact`. -/
theorem exists_lps_regS {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∃ κ : ℝ, 1 ≤ κ ∧
    ∀ v w : X, (∃ q ∈ G.regS η, dist v q < δ) → dist v w < δ →
      G.bracketU v w ∈ G.W .cu v ∧ G.dW .cu v (G.bracketU v w) ≤ κ * dist v w ∧
        G.bracketU v w ∈ G.W .s w ∧ G.dW .s w (G.bracketU v w) ≤ κ * dist v w := by
  obtain ⟨δ, hδ, κ, hκ, h⟩ := G.lps (G.regS η) (G.isCompact_regS η) (G.regS_subset_Reg hη)
  refine ⟨δ, hδ, κ, hκ, fun v w hv hvw => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := (h v w hv hvw).2
  exact ⟨h1, h2, h3, h4⟩

/-- Within the local product scale, a bracket center lies in the local plaque of its second
argument's center plaque (used by `geo:exact-cover`). -/
theorem bracketS_mem_Wloc_cs {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p x : X, (∃ q ∈ Q, dist p q < δ) → dist p x < δ →
      G.bracketS p x ∈ G.Wloc .cs x := by
  obtain ⟨δ, hδ, κ, hκ, h⟩ := G.lps Q hQ hQR
  have hκpos : 0 < κ := by linarith
  refine ⟨min δ (G.rLeaf / κ), lt_min hδ (div_pos G.rLeaf_pos hκpos), fun p x hp hpx => ?_⟩
  have hp' : ∃ q ∈ Q, dist p q < δ := by
    obtain ⟨q, hq, hpq⟩ := hp
    exact ⟨q, hq, lt_of_lt_of_le hpq (min_le_left _ _)⟩
  have hpx' : dist p x < δ := lt_of_lt_of_le hpx (min_le_left _ _)
  obtain ⟨-, -, hmem, hle, -⟩ := (h p x hp' hpx').1
  refine ⟨hmem, lt_of_le_of_lt hle ?_⟩
  have hlt : dist p x < G.rLeaf / κ := lt_of_lt_of_le hpx (min_le_right _ _)
  rwa [lt_div_iff₀ hκpos, mul_comm] at hlt

/-! ### `geo:plaque-expansivity`: forward expansivity on local unstable plaques -/

/-- Forward expansivity on local unstable plaques over a compact regular set: there are
`a, ε₀ > 0` such that for `p ∈ Q` the closed plaque `cl (plaque .u ε₀ p)` is regular, and
two of its points whose forward orbits stay `a`-close coincide. Blueprint node
`geo:plaque-expansivity`. -/
theorem plaque_expansivity {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p ∈ Q,
      closure (G.plaque .u ε₀ p) ⊆ G.Reg ∧
      ∀ y ∈ closure (G.plaque .u ε₀ p), ∀ z ∈ closure (G.plaque .u ε₀ p),
        (∀ t : ℝ, 0 ≤ t → dist (G.φ t y) (G.φ t z) ≤ a) → y = z := by
  have hshift : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ p ∈ Q, ∀ y ∈ closure (G.plaque .u ε₁ p), ∀ s : ℝ,
      |s| ≤ 2 * G.rExp → G.φ s y ∈ closure (G.plaque .u ε₁ p) → G.φ s y = y :=
    G.plaque_transverse_u Q hQ hQR
  obtain ⟨ε₁, hε₁, hsh⟩ := hshift
  obtain ⟨ρ, hρ, hρQ⟩ := hQ.exists_thickening_subset_open G.isOpen_Reg hQR
  have hC : 0 < G.CLeaf := lt_of_lt_of_le one_pos G.one_le_CLeaf
  have hrE := G.rExp_pos
  set ε₀ : ℝ := min (min ε₁ (G.rLeaf / 2)) (min (ρ / (2 * G.CLeaf)) (G.rExp / G.CLeaf))
    with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (lt_min hε₁ (half_pos G.rLeaf_pos))
    (lt_min (div_pos hρ (by linarith)) (div_pos hrE hC))
  have hε₀1 : ε₀ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀2 : ε₀ ≤ G.rLeaf / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀3 : ε₀ ≤ ρ / (2 * G.CLeaf) := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀4 : ε₀ ≤ G.rExp / G.CLeaf := (min_le_right _ _).trans (min_le_right _ _)
  have hCε₀ : G.CLeaf * ε₀ ≤ G.rExp := by
    have := (le_div_iff₀ hC).mp hε₀4
    linarith
  have hCε₀' : G.CLeaf * ε₀ < ρ := by
    have := (le_div_iff₀ (by linarith)).mp hε₀3
    linarith
  refine ⟨2 * G.rExp, by linarith, ε₀, hε₀, fun p hp => ?_⟩
  have hball : G.plaque .u ε₀ p ⊆ Metric.closedBall p (G.CLeaf * ε₀) := by
    intro y hy
    obtain ⟨hyW, hyd⟩ := hy
    rw [Metric.mem_closedBall, dist_comm]
    calc dist p y ≤ G.CLeaf * G.dW .u p y :=
          G.dist_le_CLeaf_mul_dW _ _ _ hyW (by linarith [G.rLeaf_pos])
      _ ≤ G.CLeaf * ε₀ := mul_le_mul_of_nonneg_left hyd.le hC.le
  have hcl : closure (G.plaque .u ε₀ p) ⊆ Metric.closedBall p (G.CLeaf * ε₀) :=
    closure_minimal hball Metric.isClosed_closedBall
  have hReg : closure (G.plaque .u ε₀ p) ⊆ G.Reg := by
    intro y hy
    apply hρQ
    rw [Metric.mem_thickening_iff]
    exact ⟨p, hp, lt_of_le_of_lt (hcl hy) hCε₀'⟩
  refine ⟨hReg, fun y hy z hz hfwd => ?_⟩
  -- backward control, passed to the closure through the closed set of controlled pairs
  have hback : ∀ t : ℝ, 0 ≤ t →
      dist (G.φ (-t) y) (G.φ (-t) z) ≤ 2 * G.CLeaf * ε₀ := by
    intro t ht
    have hcont : Continuous fun q : X × X => dist (G.φ (-t) q.1) (G.φ (-t) q.2) :=
      ((G.φ.continuous_toFun (-t)).comp continuous_fst).dist
        ((G.φ.continuous_toFun (-t)).comp continuous_snd)
    have hclosed :
        IsClosed {q : X × X | dist (G.φ (-t) q.1) (G.φ (-t) q.2) ≤ 2 * G.CLeaf * ε₀} :=
      isClosed_le hcont continuous_const
    have hsub : G.plaque .u ε₀ p ×ˢ G.plaque .u ε₀ p ⊆
        {q : X × X | dist (G.φ (-t) q.1) (G.φ (-t) q.2) ≤ 2 * G.CLeaf * ε₀} := by
      rintro ⟨y', z'⟩ ⟨⟨hy'W, hy'd⟩, ⟨hz'W, hz'd⟩⟩
      have hz'y' : z' ∈ G.W .u y' := by rw [G.W_eq_of_mem _ _ _ hy'W]; exact hz'W
      have hpy' : p ∈ G.W .u y' := by rw [G.W_eq_of_mem _ _ _ hy'W]; exact G.mem_W _ _
      have hd : G.dW .u y' z' < 2 * ε₀ := by
        calc G.dW .u y' z' ≤ G.dW .u y' p + G.dW .u p z' := G.dW_triangle _ _ _ _ hpy' hz'y'
          _ < 2 * ε₀ := by rw [G.dW_comm .u y' p]; linarith
      have h1 := G.dW_u_flow_le y' z' hz'y' t ht
      have hmem := G.mem_W_flow hz'y' (-t)
      change dist (G.φ (-t) y') (G.φ (-t) z') ≤ 2 * G.CLeaf * ε₀
      calc dist (G.φ (-t) y') (G.φ (-t) z')
          ≤ G.CLeaf * G.dW .u (G.φ (-t) y') (G.φ (-t) z') :=
            G.dist_le_CLeaf_mul_dW _ _ _ hmem (lt_of_le_of_lt h1 (by linarith))
        _ ≤ G.CLeaf * (2 * ε₀) := mul_le_mul_of_nonneg_left (h1.trans hd.le) hC.le
        _ = 2 * G.CLeaf * ε₀ := by ring
    have hmem : (y, z) ∈ closure (G.plaque .u ε₀ p ×ˢ G.plaque .u ε₀ p) := by
      rw [closure_prod_eq]; exact Set.mk_mem_prod hy hz
    exact closure_minimal hsub hclosed hmem
  have hall : ∀ t : ℝ, dist (G.φ t z) (G.φ t y) ≤ 2 * G.rExp := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [dist_comm]; exact hfwd t ht
    · have := hback (-t) (by linarith)
      rw [neg_neg, dist_comm] at this
      linarith
  obtain ⟨s, hs, hzs⟩ := G.expansive y (hReg hy) z hall
  have hmono : closure (G.plaque .u ε₀ p) ⊆ closure (G.plaque .u ε₁ p) :=
    closure_mono fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 hε₀1⟩
  have hsy : G.φ s y ∈ closure (G.plaque .u ε₁ p) := by rw [← hzs]; exact hmono hz
  rw [hzs]
  exact (hsh p hp y (hmono hy) s hs hsy).symm

/-- Backward expansivity on local stable plaques, the time-reversed twin of
`plaque_expansivity`, for the backward decoder. Blueprint node `geo:plaque-expansivity`. -/
theorem plaque_expansivity_backward {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p ∈ Q,
      closure (G.plaque .s ε₀ p) ⊆ G.Reg ∧
      ∀ y ∈ closure (G.plaque .s ε₀ p), ∀ z ∈ closure (G.plaque .s ε₀ p),
        (∀ t : ℝ, 0 ≤ t → dist (G.φ (-t) y) (G.φ (-t) z) ≤ a) → y = z := by
  have hshift : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ p ∈ Q, ∀ y ∈ closure (G.plaque .s ε₁ p), ∀ s : ℝ,
      |s| ≤ 2 * G.rExp → G.φ s y ∈ closure (G.plaque .s ε₁ p) → G.φ s y = y :=
    G.plaque_transverse_s Q hQ hQR
  obtain ⟨ε₁, hε₁, hsh⟩ := hshift
  obtain ⟨ρ, hρ, hρQ⟩ := hQ.exists_thickening_subset_open G.isOpen_Reg hQR
  have hC : 0 < G.CLeaf := lt_of_lt_of_le one_pos G.one_le_CLeaf
  have hrE := G.rExp_pos
  set ε₀ : ℝ := min (min ε₁ (G.rLeaf / 2)) (min (ρ / (2 * G.CLeaf)) (G.rExp / G.CLeaf))
    with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (lt_min hε₁ (half_pos G.rLeaf_pos))
    (lt_min (div_pos hρ (by linarith)) (div_pos hrE hC))
  have hε₀1 : ε₀ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀2 : ε₀ ≤ G.rLeaf / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀3 : ε₀ ≤ ρ / (2 * G.CLeaf) := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀4 : ε₀ ≤ G.rExp / G.CLeaf := (min_le_right _ _).trans (min_le_right _ _)
  have hCε₀ : G.CLeaf * ε₀ ≤ G.rExp := by
    have := (le_div_iff₀ hC).mp hε₀4
    linarith
  have hCε₀' : G.CLeaf * ε₀ < ρ := by
    have := (le_div_iff₀ (by linarith)).mp hε₀3
    linarith
  refine ⟨2 * G.rExp, by linarith, ε₀, hε₀, fun p hp => ?_⟩
  have hball : G.plaque .s ε₀ p ⊆ Metric.closedBall p (G.CLeaf * ε₀) := by
    intro y hy
    obtain ⟨hyW, hyd⟩ := hy
    rw [Metric.mem_closedBall, dist_comm]
    calc dist p y ≤ G.CLeaf * G.dW .s p y :=
          G.dist_le_CLeaf_mul_dW _ _ _ hyW (by linarith [G.rLeaf_pos])
      _ ≤ G.CLeaf * ε₀ := mul_le_mul_of_nonneg_left hyd.le hC.le
  have hcl : closure (G.plaque .s ε₀ p) ⊆ Metric.closedBall p (G.CLeaf * ε₀) :=
    closure_minimal hball Metric.isClosed_closedBall
  have hReg : closure (G.plaque .s ε₀ p) ⊆ G.Reg := by
    intro y hy
    apply hρQ
    rw [Metric.mem_thickening_iff]
    exact ⟨p, hp, lt_of_le_of_lt (hcl hy) hCε₀'⟩
  refine ⟨hReg, fun y hy z hz hbwd => ?_⟩
  -- forward control, passed to the closure through the closed set of controlled pairs
  have hfwd : ∀ t : ℝ, 0 ≤ t →
      dist (G.φ t y) (G.φ t z) ≤ 2 * G.CLeaf * ε₀ := by
    intro t ht
    have hcont : Continuous fun q : X × X => dist (G.φ t q.1) (G.φ t q.2) :=
      ((G.φ.continuous_toFun t).comp continuous_fst).dist
        ((G.φ.continuous_toFun t).comp continuous_snd)
    have hclosed :
        IsClosed {q : X × X | dist (G.φ t q.1) (G.φ t q.2) ≤ 2 * G.CLeaf * ε₀} :=
      isClosed_le hcont continuous_const
    have hsub : G.plaque .s ε₀ p ×ˢ G.plaque .s ε₀ p ⊆
        {q : X × X | dist (G.φ t q.1) (G.φ t q.2) ≤ 2 * G.CLeaf * ε₀} := by
      rintro ⟨y', z'⟩ ⟨⟨hy'W, hy'd⟩, ⟨hz'W, hz'd⟩⟩
      have hz'y' : z' ∈ G.W .s y' := by rw [G.W_eq_of_mem _ _ _ hy'W]; exact hz'W
      have hpy' : p ∈ G.W .s y' := by rw [G.W_eq_of_mem _ _ _ hy'W]; exact G.mem_W _ _
      have hd : G.dW .s y' z' < 2 * ε₀ := by
        calc G.dW .s y' z' ≤ G.dW .s y' p + G.dW .s p z' := G.dW_triangle _ _ _ _ hpy' hz'y'
          _ < 2 * ε₀ := by rw [G.dW_comm .s y' p]; linarith
      have h1 := G.dW_s_flow_le y' z' hz'y' t ht
      have hmem := G.mem_W_flow hz'y' t
      change dist (G.φ t y') (G.φ t z') ≤ 2 * G.CLeaf * ε₀
      calc dist (G.φ t y') (G.φ t z')
          ≤ G.CLeaf * G.dW .s (G.φ t y') (G.φ t z') :=
            G.dist_le_CLeaf_mul_dW _ _ _ hmem (lt_of_le_of_lt h1 (by linarith))
        _ ≤ G.CLeaf * (2 * ε₀) := mul_le_mul_of_nonneg_left (h1.trans hd.le) hC.le
        _ = 2 * G.CLeaf * ε₀ := by ring
    have hmem : (y, z) ∈ closure (G.plaque .s ε₀ p ×ˢ G.plaque .s ε₀ p) := by
      rw [closure_prod_eq]; exact Set.mk_mem_prod hy hz
    exact closure_minimal hsub hclosed hmem
  have hall : ∀ t : ℝ, dist (G.φ t z) (G.φ t y) ≤ 2 * G.rExp := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · have := hfwd t ht
      rw [dist_comm] at this
      linarith
    · have := hbwd (-t) (by linarith)
      rw [neg_neg, dist_comm] at this
      exact this
  obtain ⟨s, hs, hzs⟩ := G.expansive y (hReg hy) z hall
  have hmono : closure (G.plaque .s ε₀ p) ⊆ closure (G.plaque .s ε₁ p) :=
    closure_mono fun w hw => ⟨hw.1, lt_of_lt_of_le hw.2 hε₀1⟩
  have hsy : G.φ s y ∈ closure (G.plaque .s ε₁ p) := by rw [← hzs]; exact hmono hz
  rw [hzs]
  exact (hsh p hp y (hmono hy) s hs hsy).symm

/-- The backward-orbit control used in the proof of `plaque_expansivity`: on a common
unstable leaf, backward distances are bounded by the unstable leaf distance.
Blueprint node `geo:plaque-expansivity`. -/
theorem dist_flow_neg_le_of_mem_W_u {y z : X} (hz : z ∈ G.W .u y) (hr : G.dW .u y z < G.rLeaf)
    (t : ℝ) (ht : 0 ≤ t) :
    dist (G.φ (-t) y) (G.φ (-t) z) ≤ G.CLeaf * G.dW .u y z := by
  have h1 := G.dW_u_flow_le y z hz t ht
  have hmem := G.mem_W_flow hz (-t)
  calc dist (G.φ (-t) y) (G.φ (-t) z)
      ≤ G.CLeaf * G.dW .u (G.φ (-t) y) (G.φ (-t) z) :=
        G.dist_le_CLeaf_mul_dW _ _ _ hmem (lt_of_le_of_lt h1 hr)
    _ ≤ G.CLeaf * G.dW .u y z :=
        mul_le_mul_of_nonneg_left h1 (by linarith [G.one_le_CLeaf])

/-- A small time shift of a point of a local unstable plaque that stays in the plaque is
trivial (transversality of strong unstable plaques to the flow, uniformly over a compact
regular set). Blueprint node `geo:plaque-expansivity`. -/
theorem flow_shift_eq_of_mem_plaque_u {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ r : ℝ, 0 < r ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p ∈ Q, ∀ y ∈ G.plaque .u ε₀ p,
      ∀ s : ℝ, |s| ≤ r → G.φ s y ∈ G.plaque .u ε₀ p → G.φ s y = y := by
  obtain ⟨ε₁, hε₁, h⟩ := G.plaque_transverse_u Q hQ hQR
  exact ⟨2 * G.rExp, by linarith [G.rExp_pos], ε₁, hε₁, fun p hp y hy s hs hsy ↦
    h p hp y (subset_closure hy) s hs (subset_closure hsy)⟩

/-! ### `geo:leafwise-contraction`: consequences of G5 and G6 used by Chapter E -/

/-- Rate comparison along a short center stable leg: for `a ∈ W^{cs}_loc(x)` close to `x`,
the unstable rates along the forward orbits of `a` and `x` differ by less than `ρ`.
Uses `center_leg_cs` and uniform continuity of `lamU`. Blueprint node
`geo:leafwise-contraction` (orbit comparison, cf. BSN `cor:orbcomp`). -/
theorem lamU_flow_close_of_cs_leg (ρ : ℝ) (hρ : 0 < ρ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x a : X, a ∈ G.W .cs x → G.dW .cs x a < δ → ∀ s : ℝ, 0 ≤ s →
      |G.lamU (G.φ s a) - G.lamU (G.φ s x)| < ρ := by
  obtain ⟨δ₁, hδ₁, hu⟩ := Metric.uniformContinuous_iff.mp G.uniformContinuous_lamU ρ hρ
  have hCc := G.Cc_nonneg
  refine ⟨min G.rLeaf (δ₁ / (G.Cc + 1)),
    lt_min G.rLeaf_pos (div_pos hδ₁ (by linarith)), fun x a ha hd s hs => ?_⟩
  have hd1 : G.dW .cs x a < G.rLeaf := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : G.dW .cs x a < δ₁ / (G.Cc + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hdist : dist (G.φ s a) (G.φ s x) < δ₁ := by
    calc dist (G.φ s a) (G.φ s x) ≤ G.Cc * G.dW .cs x a := G.center_leg_cs x a ha hd1 s hs
      _ ≤ G.Cc * (δ₁ / (G.Cc + 1)) := mul_le_mul_of_nonneg_left hd2.le hCc
      _ < δ₁ := by
        rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
        linarith
  rw [← Real.dist_eq]
  exact hu hdist

/-- Backward rate comparison along a short center unstable leg.
Blueprint node `geo:leafwise-contraction`. -/
theorem lamS_flow_close_of_cu_leg (ρ : ℝ) (hρ : 0 < ρ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x a : X, a ∈ G.W .cu x → G.dW .cu x a < δ → ∀ s : ℝ, 0 ≤ s →
      |G.lamS (G.φ (-s) a) - G.lamS (G.φ (-s) x)| < ρ := by
  obtain ⟨δ₁, hδ₁, hu⟩ := Metric.uniformContinuous_iff.mp G.uniformContinuous_lamS ρ hρ
  have hCc := G.Cc_nonneg
  refine ⟨min G.rLeaf (δ₁ / (G.Cc + 1)),
    lt_min G.rLeaf_pos (div_pos hδ₁ (by linarith)), fun x a ha hd s hs => ?_⟩
  have hd1 : G.dW .cu x a < G.rLeaf := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : G.dW .cu x a < δ₁ / (G.Cc + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hdist : dist (G.φ (-s) a) (G.φ (-s) x) < δ₁ := by
    calc dist (G.φ (-s) a) (G.φ (-s) x) ≤ G.Cc * G.dW .cu x a :=
          G.center_leg_cu x a ha hd1 s hs
      _ ≤ G.Cc * (δ₁ / (G.Cc + 1)) := mul_le_mul_of_nonneg_left hd2.le hCc
      _ < δ₁ := by
        rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
        linarith
  rw [← Real.dist_eq]
  exact hu hdist

/-- Birkhoff transfer along a center stable leg: the forward accumulated unstable rates of
`a ∈ W^{cs}_δ(x)` and `x` differ by at most `ρ T` on `[0, T]`. Blueprint node
`geo:leafwise-contraction` (cf. BSN `cor:birk`). -/
theorem accumulatedRate_close_of_cs_leg (ρ : ℝ) (hρ : 0 < ρ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x a : X, a ∈ G.W .cs x → G.dW .cs x a < δ → ∀ T : ℝ, 0 ≤ T →
      |G.toFlowData.accumulatedRate G.lamU T a - G.toFlowData.accumulatedRate G.lamU T x| ≤
        ρ * T := by
  obtain ⟨δ, hδ, h⟩ := G.lamU_flow_close_of_cs_leg ρ hρ
  refine ⟨δ, hδ, fun x a ha hd T hT => ?_⟩
  have hca : Continuous fun τ : ℝ => G.lamU (G.φ τ a) :=
    G.continuous_lamU.comp (G.φ.continuous continuous_id continuous_const)
  have hcx : Continuous fun τ : ℝ => G.lamU (G.φ τ x) :=
    G.continuous_lamU.comp (G.φ.continuous continuous_id continuous_const)
  unfold FlowData.accumulatedRate
  rw [← intervalIntegral.integral_sub (hca.intervalIntegrable 0 T) (hcx.intervalIntegrable 0 T)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := ρ)
    (f := fun τ => G.lamU (G.φ τ a) - G.lamU (G.φ τ x)) ?_
  · simpa [Real.norm_eq_abs, abs_of_nonneg hT] using hb
  · intro τ hτ
    rw [Set.uIoc_of_le hT] at hτ
    rw [Real.norm_eq_abs]
    exact (h x a ha hd τ hτ.1.le).le

/-- Leafwise unstable contraction in the form used by `geo:bracket-approx`: the backward
image of a short unstable leg based at `b = φ T a` has length controlled by the accumulated
unstable rate along the forward orbit of `a` (time reversal `s = T - τ` in G5).
Blueprint node `geo:leafwise-contraction`. -/
theorem dW_u_flow_neg_le_of_accumulatedRate (β : ℝ) (hβ : 0 < β) : ∃ δ : ℝ, 0 < δ ∧
    ∀ (a c : X) (T : ℝ), 0 ≤ T → c ∈ G.W .u (G.φ T a) → G.dW .u (G.φ T a) c < δ →
      G.dW .u a (G.φ (-T) c) ≤
        G.dW .u (G.φ T a) c *
          Real.exp (-(G.toFlowData.accumulatedRate G.lamU T a - β * T)) := by
  obtain ⟨δ, hδ, h⟩ := G.leafwise_contraction_u β hβ
  refine ⟨δ, hδ, fun a c T hT hc hd => ?_⟩
  have key := h (G.φ T a) (G.φ T a) c T hT (G.mem_W _ _) (by rw [G.dW_self]; exact hδ) hc hd
  have e1 : G.φ (-T) (G.φ T a) = a := by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have e2 : ∀ τ : ℝ, G.φ (-τ) (G.φ T a) = G.φ (T - τ) a := fun τ => by
    rw [← Flow.map_add, sub_eq_neg_add]
  have e3 : (∫ τ in (0 : ℝ)..T, G.lamU (G.φ (-τ) (G.φ T a))) =
      G.toFlowData.accumulatedRate G.lamU T a := by
    unfold FlowData.accumulatedRate
    simp_rw [e2]
    rw [intervalIntegral.integral_comp_sub_left (fun s => G.lamU (G.φ s a)) T]
    simp
  rw [e1, e3] at key
  exact key

/-- Stable counterpart for `geo:bracket-approx` in backward time.
Blueprint node `geo:leafwise-contraction`. -/
theorem dW_s_flow_le_of_accumulatedRateBackward (β : ℝ) (hβ : 0 < β) : ∃ δ : ℝ, 0 < δ ∧
    ∀ (a c : X) (T : ℝ), 0 ≤ T → c ∈ G.W .s (G.φ (-T) a) → G.dW .s (G.φ (-T) a) c < δ →
      G.dW .s a (G.φ T c) ≤
        G.dW .s (G.φ (-T) a) c *
          Real.exp (-(G.toFlowData.accumulatedRateBackward G.lamS T a - β * T)) := by
  obtain ⟨δ, hδ, h⟩ := G.leafwise_contraction_s β hβ
  refine ⟨δ, hδ, fun a c T hT hc hd => ?_⟩
  have key := h (G.φ (-T) a) (G.φ (-T) a) c T hT (G.mem_W _ _) (by rw [G.dW_self]; exact hδ) hc hd
  have e1 : G.φ T (G.φ (-T) a) = a := by
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have e2 : ∀ τ : ℝ, G.φ τ (G.φ (-T) a) = G.φ (-(T - τ)) a := fun τ => by
    rw [← Flow.map_add, neg_sub, sub_eq_add_neg]
  have e3 : (∫ τ in (0 : ℝ)..T, G.lamS (G.φ τ (G.φ (-T) a))) =
      G.toFlowData.accumulatedRateBackward G.lamS T a := by
    unfold FlowData.accumulatedRateBackward
    simp_rw [e2]
    rw [intervalIntegral.integral_comp_sub_left (fun s => G.lamS (G.φ (-s) a)) T]
    simp
  rw [e1, e3] at key
  exact key

/-! ### Flow boxes: `geo:flow-box-localization` (geometric half) -/

/-- Every point lies in some inner box, hence in some box domain.
Blueprint node `geo:flow-box-localization`. -/
theorem exists_box_mem (x : X) : ∃ j, x ∈ G.innerBox j ∧ x ∈ (G.box j).U := by
  have hx : x ∈ ⋃ j, G.innerBox j := by rw [G.innerBox_cover]; exact Set.mem_univ x
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact ⟨j, hj, G.closure_innerBox_subset j (subset_closure hj)⟩

/-- The section point of a box is on the section and is a bounded time shift of the point.
Blueprint node `geo:flow-box-localization`. -/
theorem proj_spec {j : Fin G.nBoxes} {x : X} (hx : x ∈ (G.box j).U) :
    (G.box j).proj x ∈ (G.box j).D ∧ |(G.box j).τ x| < (G.box j).a := by
  exact ⟨(G.box j).flow_τ_mem x hx, (G.box j).abs_τ_lt x hx⟩

/-- The unshifted transverse estimate (`s = 0` in G11). -/
theorem transverse_estimate_zero (x : X) (hx : x ∈ G.Reg) (j : Fin G.nBoxes)
    (hxj : x ∈ (G.box j).U) :
    ∃ V : Set X, IsOpen V ∧ (G.box j).proj x ∈ V ∧ ∃ Ltr : ℝ, 0 < Ltr ∧
      ∀ y ∈ (G.box j).D ∩ V,
        dist y ((G.box j).proj x) ≤
          Ltr * max (Metric.infDist y (G.Wloc .cs x)) (Metric.infDist y (G.Wloc .cu x)) := by
  have h0 : ∀ y : X, G.φ (-(0 : ℝ)) y = y := fun y ↦ by rw [neg_zero, Flow.map_zero_apply]
  have h0' : ∀ y : X, G.φ (0 : ℝ) y = y := fun y ↦ Flow.map_zero_apply _ y
  have hxj' : G.φ (-(0 : ℝ)) x ∈ (G.box j).U := by rw [h0]; exact hxj
  obtain ⟨V, hV, hzV, Ltr, hLtr, h⟩ := G.transverse_estimate x hx j 0 hxj'
  rw [h0, h0'] at hzV
  refine ⟨V, hV, hzV, Ltr, hLtr, fun y hy ↦ ?_⟩
  have hy' : y ∈ G.φ (0 : ℝ) '' (G.box j).D ∩ V := ⟨⟨y, hy.1, h0' y⟩, hy.2⟩
  have := h y hy'
  rwa [h0, h0'] at this

/-- The common bound on all local times, used as the `|t₀| ≤ a` of
`geo:flow-coordinate`. Blueprint node `geo:flow-box-localization`. -/
noncomputable def aMax : ℝ := ∑ j : Fin G.nBoxes, (G.box j).a

/-- Every local time is bounded by `aMax`. Blueprint node `geo:flow-box-localization`. -/
theorem abs_τ_le_aMax {j : Fin G.nBoxes} {x : X} (hx : x ∈ (G.box j).U) :
    |(G.box j).τ x| ≤ G.aMax := by
  have h1 := (G.box j).abs_τ_lt x hx
  unfold aMax
  exact h1.le.trans
    (Finset.single_le_sum (f := fun i => (G.box i).a) (fun i _ => (G.box i).a_pos.le)
      (Finset.mem_univ j))

end GeodesicReconstructionData

end Kolmogorov.PointToSet
