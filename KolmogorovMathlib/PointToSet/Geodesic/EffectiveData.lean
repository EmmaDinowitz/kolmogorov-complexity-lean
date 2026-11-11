/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import GeodesicInterface.GeometricData
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface
import KolmogorovMathlib.Oracle.Closure
import KolmogorovMathlib.PointToSet.ComputableMetric.Points
import KolmogorovMathlib.PointToSet.ComputableMetric.CeOpen
import KolmogorovMathlib.PointToSet.ComputableMetric.Compact
import KolmogorovMathlib.PointToSet.ComputableMetric.Represented

/-!
# Effective standing data (geodesic blueprint, Chapter C)

The node `geo:effective-data` of `geodesic_upper_bound_blueprint.md`: the base oracle `B`
above which every algorithm of the reconstruction argument runs, and the consequences used
downstream. The structure records only what the library has no notion for: admissibility of
`B` for the time-one map with the unit potential (forward and backward), the flow at rational
times, the enumeration of marked points and the flow-box atlas. The effective quadrature of
the rates (OTL §1, "effective quadrature of `λ^{s/u}`") is *assumed* through the
admissibility fields rather than derived from `lamU_represented`/`lamS_represented`; that
derivation is an open, optional lemma (plan in `sorry_notes/NOTES_C.md`).

The library already provides relative computability of the metric table
(`ComputablePresentationIn`), represented maps between presentations (`IsRepresentedMapIn`),
Cauchy names (`IsCauchyName`), relatively enumerable predicates (`IsREIn`) and computable
real families (`IsComputableRealFamilyIn`), and `ComputableMetric/{Points, CeOpen, Compact,
Represented}.lean` provide the four further notions the geometric data use:

* `IsComputablePointIn`: a point with a relatively computable Cauchy name;
* `IsRepresentedFamilyIn`: a family of maps represented uniformly in a primcodable index
  (used for the flow at rational times, avoiding a product presentation);
* `IsRepresentedOnIn`: a map represented on a subset only (the local time and projection of a
  flow box are continuous only on its domain);
* `IsComputablyCompactIn`: a compact set whose containment in a finite union of basic balls
  is semidecidable (effective compactness data, OTL §1).

The sets `P^±` of the controlled-return definition need no effectiveness (blueprint
`geo:effective-data`, remark); nothing about them appears here.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-! ### `geo:effective-data`: the base oracle -/

variable [CompactSpace X]

/-- The effective standing data relative to an oracle `B`: the metric table, the flow at
rational times, the two rates and the two unit potentials (as admissibility of `B` for
`(f, u⁺)` and `(f⁻¹, u⁻)`), an enumeration of marked points (a dense set of oracle points;
periodicity is not used) with computable names and computably compact plaques, and the
flow-box atlas with its local times, projections, inner boxes and dense computable sequences on
the sections.
Blueprint node `geo:effective-data` (items 1–5). -/
structure EffectiveGeodesicData (G : GeodesicReconstructionData X) (P : Presentation X)
    (B : Set ℕ) where
  /-- (1) The metric table is `B`-computable. -/
  presentation : ComputablePresentationIn P B
  /-- (2) The flow is represented at rational times, uniformly in the time. -/
  flow_represented : IsRepresentedFamilyIn P P B fun q : ℚ ↦ G.φ (q : ℝ)
  /-- (3) The unstable rate is a represented real function. -/
  lamU_represented : IsRepresentedMapIn P realPresentation B G.lamU
  /-- (3) The stable rate is a represented real function. -/
  lamS_represented : IsRepresentedMapIn P realPresentation B G.lamS
  /-- (3) The base oracle is admissible for the time-one map with the forward unit potential
  (the effective quadrature of `lamU` along the flow is assumed, not derived). -/
  admissible_f : IsAdmissible P G.f (fun _ : Fin 1 ↦ G.uPlus) B
  /-- (3) … and for its inverse with the backward unit potential. -/
  admissible_finv : IsAdmissible P G.finv (fun _ : Fin 1 ↦ G.uMinus) B
  /-- (4) The enumeration of marked points (a dense set of oracle points; periodicity is not
  used). -/
  pIdx : ℕ → X
  /-- (4) The enumeration is dense. -/
  pIdx_dense : Dense (range pIdx)
  /-- (4) Enumerated points have names computable uniformly in the index. -/
  pIdx_names : ∃ a : ℕ → ℕ → ℕ, ComputableIn {charOracle B} (fun kp : ℕ × ℕ ↦ a kp.1 kp.2) ∧
    ∀ k, IsCauchyName P (pIdx k) (a k)
  /-- (4) The unstable plaques are computably compact uniformly in the index and the (positive
  rational) radius; at nonpositive radii the family is empty, since `Kplaque_spec` says nothing
  there. -/
  Kplaque_cc : IsComputablyCompactFamilyIn P B fun kr : ℕ × ℚ ↦
    if 0 < kr.2 then G.Kplaque kr.2 (pIdx kr.1) else ∅
  /-- (4) The stable plaques are computably compact uniformly in the index and the radius. -/
  Kplaque'_cc : IsComputablyCompactFamilyIn P B fun kr : ℕ × ℚ ↦
    if 0 < kr.2 then G.Kplaque' kr.2 (pIdx kr.1) else ∅
  /-- (5) Local times of the boxes are represented on the box domains. -/
  box_τ : ∀ j, IsRepresentedOnIn P realPresentation B (G.box j).U (G.box j).τ
  /-- (5) Section projections are represented on the box domains. -/
  box_proj : ∀ j, IsRepresentedOnIn P P B (G.box j).U (G.box j).proj
  /-- (5) The inner boxes are c.e. open uniformly in the index. -/
  innerBox_ceOpen : IsCeOpenFamilyIn P B G.innerBox
  /-- (5) The closures of the inner boxes are computably compact uniformly in the index. -/
  innerBox_cc : IsComputablyCompactFamilyIn P B fun j ↦ closure (G.innerBox j)
  /-- (5) A dense sequence on each section. -/
  secPt : Fin G.nBoxes → ℕ → X
  /-- (5) Section points lie on the section. -/
  secPt_mem : ∀ j k, secPt j k ∈ (G.box j).D
  /-- (5) Section points are dense in the section. -/
  secPt_dense : ∀ j, (G.box j).D ⊆ closure (range (secPt j))
  /-- (5) Section points have names computable uniformly in the box and the index. -/
  secPt_names : ∃ a : Fin G.nBoxes → ℕ → ℕ → ℕ,
    ComputableIn {charOracle B} (fun d : Fin G.nBoxes × ℕ × ℕ ↦ a d.1 d.2.1 d.2.2) ∧
      ∀ j k, IsCauchyName P (secPt j k) (a j k)

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### Consequences: admissibility for the library's point-to-set theorems -/

/-- The time-one map is a represented map. -/
theorem f_represented : IsRepresentedMapIn P P B G.f := by
  have h := IsRepresentedFamilyIn.apply P P B E.flow_represented 1
  simp only [Rat.cast_one] at h
  exact h

/-- The inverse time-one map is a represented map. -/
theorem finv_represented : IsRepresentedMapIn P P B G.finv := by
  have h := IsRepresentedFamilyIn.apply P P B E.flow_represented (-1)
  simp only [Rat.cast_neg, Rat.cast_one] at h
  exact h

/-- The forward unit potential is a represented real function (projection of the
admissibility field `admissible_f`; the effective quadrature of `lamU` along the represented
flow is assumed there). Blueprint node `geo:effective-data` (item 3). -/
theorem uPlus_represented : IsRepresentedMapIn P realPresentation B G.uPlus :=
  E.admissible_f.2.2 0

/-- The backward unit potential is a represented real function (projection of
`admissible_finv`). -/
theorem uMinus_represented : IsRepresentedMapIn P realPresentation B G.uMinus :=
  E.admissible_finv.2.2 0

/-- The base oracle is admissible for the forward data `(f, u⁺)`, which is the hypothesis of
`bsPointToSet_cone` and `IsAdmissible`-based library lemmas.
Blueprint node `geo:effective-data` (consequence). -/
theorem isAdmissible_f : IsAdmissible P G.f (fun _ : Fin 1 ↦ G.uPlus) B :=
  E.admissible_f

/-- The base oracle is admissible for the backward data `(f⁻¹, u⁻)`. -/
theorem isAdmissible_finv : IsAdmissible P G.finv (fun _ : Fin 1 ↦ G.uMinus) B :=
  E.admissible_finv

/-- The base oracle is admissible for both rates at once (needed when the quadrature of both
potentials runs in one program). -/
theorem isAdmissible_rates :
    IsAdmissible P G.f (fun j : Fin 2 ↦ if j = 0 then G.lamU else G.lamS) B := by
  refine ⟨E.presentation, E.f_represented, fun j ↦ ?_⟩
  fin_cases j
  · simpa using E.lamU_represented
  · simpa using E.lamS_represented

/-! ### Consequences: effective quadrature along ideal orbits -/

/-- Effective quadrature along an ideal orbit: the Birkhoff sum of `u⁺` at an ideal point is
computable uniformly in `(i, n)` (wrapper around the library's `birkhoff_computableIn`
through `isAdmissible_f`). Used for the computable scales `R₊, R₋` of
`geo:effective-neighborhoods`. -/
theorem birkhoff_uPlus_computable :
    IsComputableRealFamilyIn B fun d : ℕ × ℕ ↦ birkhoffSum G.f G.uPlus d.2 (P.ι d.1) := by
  have h := birkhoff_computableIn P G.f (fun _ : Fin 1 ↦ G.uPlus) B E.isAdmissible_f
  exact IsComputableRealFamilyIn.comp B _ h (fun d : ℕ × ℕ ↦ ((0 : Fin 1), d.2, d.1))
    ((Computable.const (0 : Fin 1)).pair (Computable.snd.pair Computable.fst))

/-- Backward effective quadrature. -/
theorem birkhoff_uMinus_computable :
    IsComputableRealFamilyIn B fun d : ℕ × ℕ ↦ birkhoffSum G.finv G.uMinus d.2 (P.ι d.1) := by
  have h := birkhoff_computableIn P G.finv (fun _ : Fin 1 ↦ G.uMinus) B E.isAdmissible_finv
  exact IsComputableRealFamilyIn.comp B _ h (fun d : ℕ × ℕ ↦ ((0 : Fin 1), d.2, d.1))
    ((Computable.const (0 : Fin 1)).pair (Computable.snd.pair Computable.fst))

/-- Enumerated marked points are computable points. -/
theorem isComputablePointIn_pIdx (k : ℕ) : IsComputablePointIn P B (E.pIdx k) := by
  obtain ⟨a, ha, h⟩ := E.pIdx_names
  exact ⟨a k, h k, ha.comp ((Computable.const k).pair Computable.id).computableIn⟩

/-- The orbit of an enumerated marked point has computable names at all rational times,
uniformly: this supplies the "past of `p`" and "future of `q`" of the shadowing description
in `geo:bracket-approx`. -/
theorem marked_orbit_names (k : ℕ) :
    ∃ b : ℚ → ℕ → ℕ, ComputableIn {charOracle B} (fun qp : ℚ × ℕ ↦ b qp.1 qp.2) ∧
      ∀ q : ℚ, IsCauchyName P (G.φ (q : ℝ) (E.pIdx k)) (b q) := by
  obtain ⟨a, ha, hcomp⟩ := E.isComputablePointIn_pIdx k
  exact IsRepresentedFamilyIn.names P P B E.presentation E.flow_represented ha hcomp

/-- Searching the enumeration for a marked point within a positive rational distance
of a computable point terminates (density), and the found index is computable from the name
and the radius. Blueprint node `geo:bracket-approx` ("enumerate marked points until a point
`q` sufficiently close to `φ T x` is certified"). -/
theorem exists_pIdx_near {x : X} {a : ℕ → ℕ} (_ha : IsCauchyName P x a)
    (_hcomp : ComputableIn {charOracle B} a) {r : ℚ} (hr : 0 < r) :
    ∃ k, dist (E.pIdx k) x < r := by
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ := E.pIdx_dense.exists_dist_lt x (ε := (r : ℝ)) (by exact_mod_cast hr)
  exact ⟨k, by rwa [dist_comm]⟩

/-- Certifying a box from time-zero data: for every `x` there is an inner box containing it,
and membership of a computable point in an inner box is semidecidable uniformly in the box.
Blueprint node `geo:flow-box-localization` (effective half). -/
theorem exists_innerBox_isREIn {x : X} {a : ℕ → ℕ} (ha : IsCauchyName P x a)
    (hcomp : ComputableIn {charOracle B} a) :
    (∃ j, x ∈ G.innerBox j) ∧ IsREIn B fun j : Fin G.nBoxes ↦ x ∈ G.innerBox j := by
  obtain ⟨Ei, hEi, hinner⟩ := E.innerBox_ceOpen
  refine ⟨?_, ?_⟩
  · have hx : x ∈ ⋃ j, G.innerBox j := by
      rw [G.innerBox_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  · have h : IsREIn B fun jb : Fin G.nBoxes × (ℕ × ℚ) ↦ Ei (jb.1, jb.2) ∧ x ∈ basicBall P jb.2 :=
      hEi.and ((isREIn_mem_basicBall P B E.presentation ha hcomp).comp Computable.snd.computableIn)
    have heq : (fun j : Fin G.nBoxes ↦ x ∈ G.innerBox j) =
        fun j ↦ ∃ b, Ei (j, b) ∧ x ∈ basicBall P b := by
      ext j
      rw [hinner j]
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    rw [heq]
    exact h.exists

/-- The section point of a computable point of a box domain is computable. -/
theorem isComputablePointIn_proj {j : Fin G.nBoxes} {x : X} (hx : x ∈ (G.box j).U)
    (hxc : IsComputablePointIn P B x) : IsComputablePointIn P B ((G.box j).proj x) :=
  IsRepresentedOnIn.map P P B E.presentation (E.box_proj j) hx hxc

/-- Section points are computable points, uniformly. -/
theorem isComputablePointIn_secPt (j : Fin G.nBoxes) (k : ℕ) :
    IsComputablePointIn P B (E.secPt j k) := by
  obtain ⟨a, ha, h⟩ := E.secPt_names
  exact ⟨a j k, h j k,
    ha.comp ((Computable.const j).pair ((Computable.const k).pair Computable.id)).computableIn⟩

/-! ### Oracle monotonicity and existence -/

omit E in
/-- Everything persists above the base oracle. Blueprint node `geo:effective-data`
(consequence; each item is a `PartrecIn` statement, monotone in the oracle). -/
def mono (E : EffectiveGeodesicData G P B) {A : Set ℕ} (hBA : charOracle B ≤ᵀ charOracle A) :
    EffectiveGeodesicData G P A where
  presentation := isComputableRealFamilyIn_mono_oracle E.presentation hBA
  flow_represented := isRepresentedFamilyIn_mono P P B hBA E.flow_represented
  lamU_represented := isRepresentedMapIn_mono_oracle E.lamU_represented hBA
  lamS_represented := isRepresentedMapIn_mono_oracle E.lamS_represented hBA
  admissible_f := ⟨isComputableRealFamilyIn_mono_oracle E.admissible_f.1 hBA,
    isRepresentedMapIn_mono_oracle E.admissible_f.2.1 hBA,
    fun j ↦ isRepresentedMapIn_mono_oracle (E.admissible_f.2.2 j) hBA⟩
  admissible_finv := ⟨isComputableRealFamilyIn_mono_oracle E.admissible_finv.1 hBA,
    isRepresentedMapIn_mono_oracle E.admissible_finv.2.1 hBA,
    fun j ↦ isRepresentedMapIn_mono_oracle (E.admissible_finv.2.2 j) hBA⟩
  pIdx := E.pIdx
  pIdx_dense := E.pIdx_dense
  pIdx_names := by
    obtain ⟨a, ha, h⟩ := E.pIdx_names
    exact ⟨a, computableIn_mono_oracle ha hBA, h⟩
  Kplaque_cc := isComputablyCompactFamilyIn_mono P B hBA E.Kplaque_cc
  Kplaque'_cc := isComputablyCompactFamilyIn_mono P B hBA E.Kplaque'_cc
  box_τ j := isRepresentedOnIn_mono P realPresentation B hBA (E.box_τ j)
  box_proj j := isRepresentedOnIn_mono P P B hBA (E.box_proj j)
  innerBox_ceOpen := isCeOpenFamilyIn_mono P B hBA E.innerBox_ceOpen
  innerBox_cc := isComputablyCompactFamilyIn_mono P B hBA E.innerBox_cc
  secPt := E.secPt
  secPt_mem := E.secPt_mem
  secPt_dense := E.secPt_dense
  secPt_names := by
    obtain ⟨a, ha, h⟩ := E.secPt_names
    exact ⟨a, computableIn_mono_oracle ha hBA, h⟩

/-- The enumeration is unchanged by strengthening the oracle. -/
theorem mono_pIdx {A : Set ℕ} (hBA : charOracle B ≤ᵀ charOracle A) :
    (E.mono hBA).pIdx = E.pIdx :=
  rfl

end EffectiveGeodesicData

/-! ### Existence: auxiliary constructions -/

section existence

variable {P : Presentation X} {Q : Presentation Y}

/-- A row of an oracle-computable integer table, read as naturals, is oracle-computable. -/
theorem computableIn_table_row {B : Set ℕ} {v : ℕ → ℕ → ℤ}
    (hv : ComputableIn {charOracle B} fun p : ℕ × ℕ ↦ v p.1 p.2) (m : ℕ) :
    ComputableIn {charOracle B} fun kp : ℕ × ℕ ↦ (v (Nat.pair m kp.1) kp.2).toNat := by
  -- terms are built without expected types: unifying against `Nat.pair` is expensive
  have h1 : Computable fun kp : ℕ × ℕ ↦ (Nat.pair m kp.1, kp.2) :=
    ((Primrec₂.natPair.comp (Primrec.const m) Primrec.fst).pair Primrec.snd).to_comp
  have h2 := hv.comp (h1.computableIn (O := {charOracle B}))
  have h3 := ComputableReals.primrec_intToNat.to_comp.computableIn.comp h2
  exact h3

end existence

/-- A base oracle exists when every section of the atlas is nonempty (the field `secPt_mem`
cannot be satisfied for an empty section): continuous data are represented above some oracle
(`exists_admissible_base`, applied to the rates and to the two unit potentials, which are
continuous by `uPlus_props`/`uMinus_props`), the sound ball relations of the flow at rational
times, of the local times and projections, the inner boxes and all compactness certificates
are coded by `exists_oracle_isREIn`, the marked points are the ideal points `P.ι k` (named by
constant sequences), and the names of dense sequences on the sections are coded into one
integer table (`oracle_joins_tables`). Blueprint node `geo:effective-data` (existence). -/
theorem exists_effectiveGeodesicData_of_nonempty (G : GeodesicReconstructionData X)
    (P : Presentation X) (hD : ∀ j, ((G.box j).D).Nonempty) :
    ∃ B : Set ℕ, Nonempty (EffectiveGeodesicData G P B) := by
  classical
  -- (4) the marked points are the ideal points, named by constant sequences
  let pIdx : ℕ → X := P.ι
  -- (5) dense sequences on the sections, with names
  have hsec : ∀ (j : Fin G.nBoxes) (n m : ℕ), ∃ y ∈ (G.box j).D,
      (∃ y' ∈ (G.box j).D, dist (P.ι n) y' < dyadicRadius m) →
        dist (P.ι n) y < dyadicRadius m := by
    intro j n m
    by_cases h : ∃ y' ∈ (G.box j).D, dist (P.ι n) y' < dyadicRadius m
    · obtain ⟨y', hy', hd⟩ := h
      exact ⟨y', hy', fun _ ↦ hd⟩
    · obtain ⟨d₀, hd₀⟩ := hD j
      exact ⟨d₀, hd₀, fun h' ↦ (h h').elim⟩
  choose sp hsmem hsdist using hsec
  let secPt : Fin G.nBoxes → ℕ → X := fun j k ↦ sp j k.unpair.1 k.unpair.2
  have hsecPt_mem : ∀ j k, secPt j k ∈ (G.box j).D := fun j k ↦ hsmem _ _ _
  have hsecPt_dense : ∀ j, (G.box j).D ⊆ closure (Set.range (secPt j)) := by
    intro j y hy
    refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
    obtain ⟨m, hm⟩ := exists_dyadicRadius_lt (show 0 < ε / 2 by positivity)
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp P.dense y (dyadicRadius m) (dyadicRadius_pos m)
    refine ⟨secPt j (Nat.pair n m), ⟨Nat.pair n m, rfl⟩, ?_⟩
    have h1 : dist (P.ι n) (sp j n m) < dyadicRadius m :=
      hsdist j n m ⟨y, hy, by rwa [dist_comm]⟩
    change dist y (sp j (Nat.pair n m).unpair.1 (Nat.pair n m).unpair.2) < ε
    rw [Nat.unpair_pair]
    calc dist y (sp j n m) ≤ dist y (P.ι n) + dist (P.ι n) (sp j n m) := dist_triangle _ _ _
      _ < dyadicRadius m + dyadicRadius m := add_lt_add hn h1
      _ < ε := by linarith
  have hsnames : ∀ (j : Fin G.nBoxes) (k : ℕ), ∃ a : ℕ → ℕ, IsCauchyName P (secPt j k) a :=
    fun j k ↦ exists_isCauchyName P _
  choose aS haS using hsnames
  -- the integer table coding the names of the section points
  let v : ℕ → ℕ → ℤ := fun n p ↦
    if n.unpair.1 = 1 then
      ((@Encodable.decode (Fin G.nBoxes × ℕ) Primcodable.toEncodable n.unpair.2).elim 0
        fun jk ↦ (aS jk.1 jk.2 p : ℤ))
    else 0
  -- (1), (3) continuous data above a base oracle
  obtain ⟨C₀, hC₀⟩ := exists_admissible_base P G.f G.toFlowData.continuous_f
    (fun j : Fin 2 ↦ if j = 0 then G.lamU else G.lamS) (fun j ↦ by
      fin_cases j
      · simpa using G.continuous_lamU
      · simpa using G.continuous_lamS)
  -- (3) the unit potentials are continuous on the compact space, hence represented above
  -- some oracle together with `f` resp. `f⁻¹`
  obtain ⟨C₈, hC₈⟩ := exists_admissible_base P G.f G.toFlowData.continuous_f
    (fun _ : Fin 1 ↦ G.uPlus) (fun _ ↦ G.uPlus_props.1.continuous)
  obtain ⟨C₉, hC₉⟩ := exists_admissible_base P G.finv G.toFlowData.continuous_finv
    (fun _ : Fin 1 ↦ G.uMinus) (fun _ ↦ G.uMinus_props.1.continuous)
  -- the sound relations and compactness certificates to be made enumerable
  let Rflow : ℚ × (ℕ × ℚ) × (ℕ × ℚ) → Prop := fun w ↦
    0 < w.2.1.2 ∧ 0 < w.2.2.2 ∧ G.φ (w.1 : ℝ) '' basicBall P w.2.1 ⊆ basicBall P w.2.2
  let RK : (ℕ × ℚ) × List (ℕ × ℚ) → Prop := fun d ↦
    (if 0 < d.1.2 then G.Kplaque d.1.2 (pIdx d.1.1) else ∅) ⊆ ⋃ b ∈ d.2, basicBall P b
  let RK' : (ℕ × ℚ) × List (ℕ × ℚ) → Prop := fun d ↦
    (if 0 < d.1.2 then G.Kplaque' d.1.2 (pIdx d.1.1) else ∅) ⊆ ⋃ b ∈ d.2, basicBall P b
  let Rτ : Fin G.nBoxes × (ℕ × ℚ) × (ℕ × ℚ) → Prop := fun w ↦
    0 < w.2.1.2 ∧ 0 < w.2.2.2 ∧
      (G.box w.1).τ '' (basicBall P w.2.1 ∩ (G.box w.1).U) ⊆ basicBall realPresentation w.2.2
  let Rproj : Fin G.nBoxes × (ℕ × ℚ) × (ℕ × ℚ) → Prop := fun w ↦
    0 < w.2.1.2 ∧ 0 < w.2.2.2 ∧
      (G.box w.1).proj '' (basicBall P w.2.1 ∩ (G.box w.1).U) ⊆ basicBall P w.2.2
  let Rinner : Fin G.nBoxes × (ℕ × ℚ) → Prop := fun w ↦ basicBall P w.2 ⊆ G.innerBox w.1
  let Rinnercc : Fin G.nBoxes × List (ℕ × ℚ) → Prop := fun d ↦
    closure (G.innerBox d.1) ⊆ ⋃ b ∈ d.2, basicBall P b
  obtain ⟨C₁, hC₁⟩ := exists_oracle_isREIn Rflow
  obtain ⟨C₂, hC₂⟩ := exists_oracle_isREIn RK
  obtain ⟨C₃, hC₃⟩ := exists_oracle_isREIn RK'
  obtain ⟨C₄, hC₄⟩ := exists_oracle_isREIn Rτ
  obtain ⟨C₅, hC₅⟩ := exists_oracle_isREIn Rproj
  obtain ⟨C₆, hC₆⟩ := exists_oracle_isREIn Rinner
  obtain ⟨C₇, hC₇⟩ := exists_oracle_isREIn Rinnercc
  let Cs : ℕ → Set ℕ := fun n ↦ match n with
    | 0 => C₁
    | 1 => C₂
    | 2 => C₃
    | 3 => C₄
    | 4 => C₅
    | 5 => C₆
    | 6 => C₇
    | 7 => C₈
    | 8 => C₉
    | _ => ∅
  obtain ⟨B, hC₀B, hCsB, hvB⟩ := oracle_joins_tables C₀ Cs v
  have hAdm := hC₀ B hC₀B
  have hflow : charOracle C₁ ≤ᵀ charOracle B := hCsB 0
  have hK : charOracle C₂ ≤ᵀ charOracle B := hCsB 1
  have hK' : charOracle C₃ ≤ᵀ charOracle B := hCsB 2
  have hτ : charOracle C₄ ≤ᵀ charOracle B := hCsB 3
  have hproj : charOracle C₅ ≤ᵀ charOracle B := hCsB 4
  have hinner : charOracle C₆ ≤ᵀ charOracle B := hCsB 5
  have hinnercc : charOracle C₇ ≤ᵀ charOracle B := hCsB 6
  have huPlus : charOracle C₈ ≤ᵀ charOracle B := hCsB 7
  have huMinus : charOracle C₉ ≤ᵀ charOracle B := hCsB 8
  refine ⟨B, ⟨{ presentation := hAdm.1
                flow_represented := ⟨Rflow, hC₁ B hflow, fun _ _ _ h ↦ h, fun q x c hx ↦
                  exists_basicBall_image_subset_of_continuousAt (P := P) (Q := P)
                    (G.φ.continuous_toFun (q : ℝ)).continuousAt hx⟩
                lamU_represented := by simpa using hAdm.2.2 0
                lamS_represented := by simpa using hAdm.2.2 1
                admissible_f := hC₈ B huPlus
                admissible_finv := hC₉ B huMinus
                pIdx := pIdx
                pIdx_dense := P.dense
                pIdx_names := ⟨fun k _ ↦ k, Computable.fst.computableIn,
                  fun k p ↦ by simpa [pIdx] using dyadicRadius_pos p⟩
                Kplaque_cc := ⟨fun kr ↦ by
                  change IsCompact (if 0 < kr.2 then G.Kplaque kr.2 (pIdx kr.1) else ∅)
                  by_cases hr : 0 < kr.2
                  · rw [ite_eq_left hr]
                    exact (G.Kplaque_spec _ kr.2 hr).1
                  · rw [ite_eq_right hr]
                    exact isCompact_empty, hC₂ B hK⟩
                Kplaque'_cc := ⟨fun kr ↦ by
                  change IsCompact (if 0 < kr.2 then G.Kplaque' kr.2 (pIdx kr.1) else ∅)
                  by_cases hr : 0 < kr.2
                  · rw [ite_eq_left hr]
                    exact (G.Kplaque'_spec _ kr.2 hr).1
                  · rw [ite_eq_right hr]
                    exact isCompact_empty, hC₃ B hK'⟩
                box_τ := fun j ↦ ⟨fun bc ↦ Rτ (j, bc),
                  (hC₄ B hτ).comp ((Computable.const j).pair Computable.id).computableIn,
                  fun _ _ h ↦ h, fun x hxU c hx ↦ ?_⟩
                box_proj := fun j ↦ ⟨fun bc ↦ Rproj (j, bc),
                  (hC₅ B hproj).comp ((Computable.const j).pair Computable.id).computableIn,
                  fun _ _ h ↦ h, fun x hxU c hx ↦ ?_⟩
                innerBox_ceOpen := ⟨Rinner, hC₆ B hinner,
                  fun j ↦ isOpen_eq_biUnion_basicBall (G.isOpen_innerBox j)⟩
                innerBox_cc := ⟨fun j ↦ isClosed_closure.isCompact, hC₇ B hinnercc⟩
                secPt := secPt
                secPt_mem := hsecPt_mem
                secPt_dense := hsecPt_dense
                secPt_names := ⟨aS, ?_, haS⟩ }⟩⟩
  · -- completeness of the local time relation on the box domain
    obtain ⟨b, ⟨hb1, hc, hsub⟩, hxb⟩ := exists_basicBall_image_subset_of_continuousAt (P := P)
      (Q := realPresentation)
      ((G.box j).continuousOn_τ.continuousAt ((G.box j).isOpen_U.mem_nhds hxU)) hx
    exact ⟨b, ⟨hb1, hc, (Set.image_mono Set.inter_subset_left).trans hsub⟩, hxb⟩
  · -- completeness of the projection relation on the box domain
    have hτx : ContinuousAt (G.box j).τ x :=
      (G.box j).continuousOn_τ.continuousAt ((G.box j).isOpen_U.mem_nhds hxU)
    have hprojx : ContinuousAt (G.box j).proj x :=
      G.φ.cont'.continuousAt.comp (hτx.prodMk continuousAt_id)
    obtain ⟨b, ⟨hb1, hc, hsub⟩, hxb⟩ :=
      exists_basicBall_image_subset_of_continuousAt (P := P) (Q := P) hprojx hx
    exact ⟨b, ⟨hb1, hc, (Set.image_mono Set.inter_subset_left).trans hsub⟩, hxb⟩
  · -- names of the section points are read off row `1` of the table
    have henc : Computable fun d : Fin G.nBoxes × ℕ × ℕ ↦
        (@Encodable.encode (Fin G.nBoxes × ℕ) Primcodable.toEncodable (d.1, d.2.1), d.2.2) :=
      (Computable.encode.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))).pair
        (Computable.snd.comp Computable.snd)
    have h2 := (computableIn_table_row hvB 1).comp (henc.computableIn (O := {charOracle B}))
    refine h2.of_eq fun d ↦ ?_
    have hv1 : v (Nat.pair 1 (@Encodable.encode (Fin G.nBoxes × ℕ) Primcodable.toEncodable
        (d.1, d.2.1))) d.2.2 = (aS d.1 d.2.1 d.2.2 : ℤ) := by
      simp only [v, Nat.unpair_pair, ↓reduceIte,
        @Encodable.encodek (Fin G.nBoxes × ℕ) Primcodable.toEncodable, Option.elim_some]
    change (v (Nat.pair 1 (@Encodable.encode (Fin G.nBoxes × ℕ) Primcodable.toEncodable
        (d.1, d.2.1))) d.2.2).toNat = aS d.1 d.2.1 d.2.2
    rw [hv1, Int.toNat_natCast]

/-- A base oracle exists: continuous data are represented above some oracle
(`exists_admissible_base`), a countable dense set of marked points with names and
compactness certificates can be coded into an oracle, and so can the finite
flow-box atlas. Blueprint node `geo:effective-data` (existence). -/
theorem exists_effectiveGeodesicData (G : GeodesicReconstructionData X) (P : Presentation X) :
    ∃ B : Set ℕ, Nonempty (EffectiveGeodesicData G P B) :=
  exists_effectiveGeodesicData_of_nonempty G P fun j ↦ (G.box j).D_nonempty

end Kolmogorov.PointToSet
