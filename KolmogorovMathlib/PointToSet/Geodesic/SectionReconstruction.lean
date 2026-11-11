/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.PlaqueNeighborhoods

/-!
# Transverse sections and local reconstruction (geodesic blueprint, Chapter G)

The nodes `geo:flow-box-localization` (effective half, OTL
`lem:effective_flowbox_localization`), `geo:transverse-estimate` (consequences of the field
G11, OTL `lem:transverse_reconstruction`), `geo:section-localization` (OTL
`cor:integral_section_localization`) and `geo:section-reconstruction` (OTL
`cor:integral_point_reconstruction`) of `geodesic_upper_bound_blueprint.md`.

The transverse estimate (G11) gives an open neighborhood `V` of the section point
`z = (box j).proj x` on which
`dist y z ≤ Ltr · max (infDist y W^{cs}_loc(x)) (infDist y W^{cu}_loc(x))`
for `y ∈ D ∩ V`. For the search the program needs a finite code of a neighborhood, so `V` is
shrunk to a basic ball `basicBall P (c, rV)` about an ideal point: the code `(c, rV)` is part
of the point-dependent localization data (decision D7), fixed once for `x` and the parameters.

With the neighborhoods `U^{cs}, U^{cu}` of Chapter F, the set `Ω = U^{cs} ∩ U^{cu} ∩ D ∩ V'`
contains `z` and lies within `Ltr C₂ max (E₊(ρ), E₋(ρ))` of it. The program enumerates the
dense computable sequence `secPt j` on the section, keeps the first point certified inside
`U^{cs} ∩ U^{cu} ∩ V'` (three semidecidable tests on a computable point), and rounds it to
precision `max (Rp, Rm)`. OTL's remark applies: an arbitrary effectively closed section would
not justify this search; the dense computable sequence on `D` is what makes it terminate.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-! ### `geo:transverse-estimate`: consequences of G11 -/

/-- Points of the section near `z` inside both thickenings are within `Ltr max (r₁, r₂)` of `z`
(OTL `lem:transverse_reconstruction`, pointwise form).
Blueprint node `geo:transverse-estimate`. -/
theorem dist_le_of_mem_thickenings (x : X) (hx : x ∈ G.Reg) {j : Fin G.nBoxes}
    (hxj : x ∈ (G.box j).U) :
    ∃ V : Set X, IsOpen V ∧ (G.box j).proj x ∈ V ∧ ∃ Ltr : ℝ, 0 < Ltr ∧
      ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        ∀ y ∈ (G.box j).D ∩ V,
          y ∈ Metric.thickening r₁ (G.Wloc .cs x) → y ∈ Metric.thickening r₂ (G.Wloc .cu x) →
            dist y ((G.box j).proj x) ≤ Ltr * max r₁ r₂ := by
  obtain ⟨V, hV, hzV, Ltr, hLtr, h⟩ := G.transverse_estimate_zero x hx j hxj
  refine ⟨V, hV, hzV, Ltr, hLtr, fun r₁ r₂ _ _ y hy hy1 hy2 ↦ ?_⟩
  obtain ⟨z₁, hz₁, hd₁⟩ := Metric.mem_thickening_iff.mp hy1
  obtain ⟨z₂, hz₂, hd₂⟩ := Metric.mem_thickening_iff.mp hy2
  have i1 : Metric.infDist y (G.Wloc .cs x) ≤ r₁ :=
    (Metric.infDist_le_dist_of_mem hz₁).trans hd₁.le
  have i2 : Metric.infDist y (G.Wloc .cu x) ≤ r₂ :=
    (Metric.infDist_le_dist_of_mem hz₂).trans hd₂.le
  exact (h y hy).trans (mul_le_mul_of_nonneg_left (max_le_max i1 i2) hLtr.le)

/-- The diameter form: the intersection of the two tubes with the section near `z` has
diameter at most `2 Ltr max (r₁, r₂)`. Blueprint node `geo:transverse-estimate`. -/
theorem diam_tubes_le (x : X) (hx : x ∈ G.Reg) {j : Fin G.nBoxes} (hxj : x ∈ (G.box j).U) :
    ∃ V : Set X, IsOpen V ∧ (G.box j).proj x ∈ V ∧ ∃ Ltr : ℝ, 0 < Ltr ∧
      ∀ r₁ r₂ : ℝ, 0 ≤ r₁ → 0 ≤ r₂ →
        Metric.diam (Metric.thickening r₁ (G.Wloc .cs x) ∩ Metric.thickening r₂ (G.Wloc .cu x) ∩
          (G.box j).D ∩ V) ≤ 2 * Ltr * max r₁ r₂ := by
  obtain ⟨V, hV, hzV, Ltr, hLtr, h⟩ := G.dist_le_of_mem_thickenings x hx hxj
  refine ⟨V, hV, hzV, Ltr, hLtr, fun r₁ r₂ hr₁ hr₂ ↦ ?_⟩
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (by positivity) (le_max_of_le_left hr₁))
  intro y hy y' hy'
  obtain ⟨⟨⟨hy1, hy2⟩, hyD⟩, hyV⟩ := hy
  obtain ⟨⟨⟨hy1', hy2'⟩, hyD'⟩, hyV'⟩ := hy'
  have e1 := h r₁ r₂ hr₁ hr₂ y ⟨hyD, hyV⟩ hy1 hy2
  have e2 := h r₁ r₂ hr₁ hr₂ y' ⟨hyD', hyV'⟩ hy1' hy2'
  calc dist y y' ≤ dist y ((G.box j).proj x) + dist y' ((G.box j).proj x) :=
        dist_triangle_right _ _ _
    _ ≤ 2 * Ltr * max r₁ r₂ := by linarith

/-- The transverse estimate needs explicit localization: tubes around the unrestricted leaves
need not meet the section only near `z` (OTL remark). This records that the estimate is
claimed on `D ∩ V` only, by restating G11 with `V` shrunk to any smaller open neighborhood. -/
theorem transverse_estimate_mono (x : X) (_hx : x ∈ G.Reg) {j : Fin G.nBoxes}
    (_hxj : x ∈ (G.box j).U) {V V' : Set X} (hV' : V' ⊆ V) {Ltr : ℝ}
    (h : ∀ y ∈ (G.box j).D ∩ V, dist y ((G.box j).proj x) ≤
      Ltr * max (Metric.infDist y (G.Wloc .cs x)) (Metric.infDist y (G.Wloc .cu x))) :
    ∀ y ∈ (G.box j).D ∩ V', dist y ((G.box j).proj x) ≤
      Ltr * max (Metric.infDist y (G.Wloc .cs x)) (Metric.infDist y (G.Wloc .cu x)) := by
  exact fun y hy ↦ h y ⟨hy.1, hV' hy.2⟩

end GeodesicReconstructionData

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### `geo:flow-box-localization`: the coded neighborhood -/

/-- Membership of a section point in a basic ball is semidecidable uniformly in `(j, k)` and in
the ball code (certificate: a name stage and the rational metric table). -/
private theorem isREIn_secPt_mem_basicBall :
    IsREIn B fun e : (Fin G.nBoxes × ℕ) × (ℕ × ℚ) ↦ E.secPt e.1.1 e.1.2 ∈ basicBall P e.2 := by
  obtain ⟨a, ha, haname⟩ := E.secPt_names
  obtain ⟨q, hq, hqerr⟩ := E.presentation
  have hpow : Computable fun m : ℕ ↦ (2 : ℚ)⁻¹ ^ m := by
    have h : Computable fun m : ℕ ↦ (Nat.rec (1 : ℚ) (fun _ ih ↦ (2 : ℚ)⁻¹ * ih) m : ℚ) :=
      Computable.nat_rec (f := fun m : ℕ ↦ m) (g := fun _ : ℕ ↦ (1 : ℚ))
        (h := fun _ p ↦ (2 : ℚ)⁻¹ * p.2) Computable.id (Computable.const 1)
        (computable₂_ratMul.comp (Computable.const (2 : ℚ)⁻¹) (Computable.snd.comp Computable.snd))
    refine h.of_eq fun m ↦ ?_
    induction m with
    | zero => simp
    | succ n ih => rw [pow_succ', ← ih]
  -- the certificate predicate, semidecidable uniformly in the point index and the ball
  have hcert : IsREIn B fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
      q ((a em.1.1.1 em.1.1.2 em.2, em.1.2.1), em.2) + 2 * (2 : ℚ)⁻¹ ^ em.2 < em.1.2.2 := by
    have hg1 : Computable fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
        (em.1.1.1, em.1.1.2, em.2) :=
      (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)
    have h1 : ComputableIn {charOracle B} fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
        a em.1.1.1 em.1.1.2 em.2 :=
      (ha.comp hg1.computableIn).of_eq fun _ ↦ rfl
    have hc1 : Computable fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦ em.1.2.1 :=
      Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hg2 : ComputableIn {charOracle B} fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
        ((a em.1.1.1 em.1.1.2 em.2, em.1.2.1), em.2) :=
      (h1.pair hc1.computableIn).pair ComputableIn.snd
    have h2 : ComputableIn {charOracle B} fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
        q ((a em.1.1.1 em.1.1.2 em.2, em.1.2.1), em.2) :=
      hq.comp hg2
    have hc2 : Computable fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦ 2 * (2 : ℚ)⁻¹ ^ em.2 :=
      computable₂_ratMul.comp (Computable.const 2) (hpow.comp Computable.snd)
    have h3 : ComputableIn {charOracle B} fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
        q ((a em.1.1.1 em.1.1.2 em.2, em.1.2.1), em.2) + 2 * (2 : ℚ)⁻¹ ^ em.2 :=
      computable₂_ratAdd.computableIn₂.comp h2 hc2.computableIn
    have hc3 : Computable fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦ em.1.2.2 :=
      Computable.snd.comp (Computable.snd.comp Computable.fst)
    have h4 : ComputableIn {charOracle B} fun em : ((Fin G.nBoxes × ℕ) × (ℕ × ℚ)) × ℕ ↦
        decide (q ((a em.1.1.1 em.1.1.2 em.2, em.1.2.1), em.2) + 2 * (2 : ℚ)⁻¹ ^ em.2 <
          em.1.2.2) :=
      computable₂_ratLt.computableIn₂.comp h3 hc3.computableIn
    exact isREIn_of_computableIn_decide B _ h4
  -- membership in a basic ball is equivalent to the existence of a certificate
  have hiff : ∀ e : (Fin G.nBoxes × ℕ) × (ℕ × ℚ), E.secPt e.1.1 e.1.2 ∈ basicBall P e.2 ↔
      ∃ m, q ((a e.1.1 e.1.2 m, e.2.1), m) + 2 * (2 : ℚ)⁻¹ ^ m < e.2.2 := by
    intro e
    constructor
    · intro hx
      have hx' : dist (E.secPt e.1.1 e.1.2) (P.ι e.2.1) < e.2.2 := Metric.mem_ball.mp hx
      obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
        (show 0 < ((e.2.2 : ℝ) - dist (E.secPt e.1.1 e.1.2) (P.ι e.2.1)) / 4 by linarith)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
      refine ⟨m, ?_⟩
      have herr := (abs_lt.mp (hqerr (a e.1.1 e.1.2 m, e.2.1) m)).2
      have hname := haname e.1.1 e.1.2 m
      unfold dyadicRadius at hname
      have htri := dist_triangle (P.ι (a e.1.1 e.1.2 m)) (E.secPt e.1.1 e.1.2) (P.ι e.2.1)
      have : ((q ((a e.1.1 e.1.2 m, e.2.1), m) + 2 * (2 : ℚ)⁻¹ ^ m : ℚ) : ℝ) < e.2.2 := by
        push_cast
        linarith
      exact_mod_cast this
    · rintro ⟨m, hm⟩
      have hm' : ((q ((a e.1.1 e.1.2 m, e.2.1), m) + 2 * (2 : ℚ)⁻¹ ^ m : ℚ) : ℝ) < e.2.2 := by
        exact_mod_cast hm
      push_cast at hm'
      have herr := (abs_lt.mp (hqerr (a e.1.1 e.1.2 m, e.2.1) m)).1
      have hname := haname e.1.1 e.1.2 m
      unfold dyadicRadius at hname
      rw [dist_comm] at hname
      have htri := dist_triangle (E.secPt e.1.1 e.1.2) (P.ι (a e.1.1 e.1.2 m)) (P.ι e.2.1)
      exact Metric.mem_ball.mpr (by linarith)
  obtain ⟨f, hf, hdom⟩ := hcert.exists
  exact ⟨f, hf, fun e ↦ (hiff e).trans (hdom e)⟩

/-- Membership of a shifted section point `φ s (secPt j k)` (rational shift `s`) in a basic ball
is semidecidable uniformly in `(j, k)`, `s` and the ball code, through the sound and complete
relation of the represented flow `E.flow_represented`. -/
private theorem isREIn_shift_mem_basicBall :
    IsREIn B fun e : (Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ) ↦
      G.φ (e.2.1 : ℝ) (E.secPt e.1.1 e.1.2) ∈ basicBall P e.2.2 := by
  obtain ⟨R, hR, hsound, hcomp⟩ := E.flow_represented
  have hiff : ∀ e : (Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ),
      G.φ (e.2.1 : ℝ) (E.secPt e.1.1 e.1.2) ∈ basicBall P e.2.2 ↔
        ∃ b : ℕ × ℚ, R (e.2.1, b, e.2.2) ∧ E.secPt e.1.1 e.1.2 ∈ basicBall P b := by
    intro e
    constructor
    · intro h
      exact hcomp e.2.1 _ _ h
    · rintro ⟨b, hb, hmem⟩
      exact (hsound _ _ _ hb).2.2 ⟨_, hmem, rfl⟩
  have hg1 : Computable fun eb : ((Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ)) × (ℕ × ℚ) ↦
      (eb.1.2.1, eb.2, eb.1.2.2) :=
    (Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hg2 : Computable fun eb : ((Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ)) × (ℕ × ℚ) ↦
      (eb.1.1, eb.2) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have h1 : IsREIn B fun eb : ((Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ)) × (ℕ × ℚ) ↦
      R (eb.1.2.1, eb.2, eb.1.2.2) :=
    IsREIn.comp (f := fun eb : ((Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ)) × (ℕ × ℚ) ↦
      (eb.1.2.1, eb.2, eb.1.2.2)) hR hg1.computableIn
  have h2 : IsREIn B fun eb : ((Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ)) × (ℕ × ℚ) ↦
      E.secPt eb.1.1.1 eb.1.1.2 ∈ basicBall P eb.2 :=
    IsREIn.comp (f := fun eb : ((Fin G.nBoxes × ℕ) × ℚ × (ℕ × ℚ)) × (ℕ × ℚ) ↦ (eb.1.1, eb.2))
      E.isREIn_secPt_mem_basicBall hg2.computableIn
  obtain ⟨f, hf, hdom⟩ := (h1.and h2).exists
  exact ⟨f, hf, fun e ↦ (hiff e).trans (hdom e)⟩

/-- Membership of a shifted section point `φ s (secPt j k)` in a basic ball, in a `ballUnion`,
and in their intersections is semidecidable uniformly in `(j, k)`, in the rational shift `s`
and in the codes: the tests of the search. Blueprint node `geo:section-reconstruction`. -/
theorem isREIn_secPt_mem :
    IsREIn B fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      G.φ (d.2.1 : ℝ) (E.secPt d.1.1 d.1.2) ∈
        ballUnion P d.2.2.1 ∩ ballUnion P d.2.2.2.1 ∩ basicBall P d.2.2.2.2 := by
  have hball := E.isREIn_shift_mem_basicBall
  -- membership in a finite union of basic balls
  have hunion : IsREIn B fun e : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) ↦
      G.φ (e.2.1 : ℝ) (E.secPt e.1.1 e.1.2) ∈ ballUnion P e.2.2 := by
    have hlist : IsREIn B fun eb : ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ)) × (ℕ × ℚ) ↦
        eb.2 ∈ eb.1.2.2 := by
      apply isREIn_of_computable_decide
      have h : Computable fun eb : ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ)) × (ℕ × ℚ) ↦
          decide (eb.1.2.2.idxOf eb.2 < eb.1.2.2.length) :=
        (PrimrecPred.decide (Primrec.nat_lt.comp
          (Primrec.list_idxOf.comp Primrec.snd
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to_comp
      refine h.of_eq fun eb ↦ ?_
      simp only [List.idxOf_lt_length_iff]
    have hgb : Computable fun eb : ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ)) × (ℕ × ℚ) ↦
        (eb.1.1, eb.1.2.1, eb.2) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
    have hb : IsREIn B fun eb : ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ)) × (ℕ × ℚ) ↦
        G.φ (eb.1.2.1 : ℝ) (E.secPt eb.1.1.1 eb.1.1.2) ∈ basicBall P eb.2 :=
      IsREIn.comp (f := fun eb : ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ)) × (ℕ × ℚ) ↦
        (eb.1.1, eb.1.2.1, eb.2)) hball hgb.computableIn
    obtain ⟨f, hf, hdom⟩ := (hlist.and hb).exists
    refine ⟨f, hf, fun e ↦ Iff.trans ?_ (hdom e)⟩
    simp only [ballUnion, Set.mem_iUnion, exists_prop]
  have g1 : Computable fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      (d.1, d.2.1, d.2.2.1) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have g2 : Computable fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      (d.1, d.2.1, d.2.2.2.1) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have g3 : Computable fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      (d.1, d.2.1, d.2.2.2.2) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have k1 : IsREIn B fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      G.φ (d.2.1 : ℝ) (E.secPt d.1.1 d.1.2) ∈ ballUnion P d.2.2.1 :=
    IsREIn.comp (f := fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      (d.1, d.2.1, d.2.2.1)) hunion g1.computableIn
  have k2 : IsREIn B fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      G.φ (d.2.1 : ℝ) (E.secPt d.1.1 d.1.2) ∈ ballUnion P d.2.2.2.1 :=
    IsREIn.comp (f := fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      (d.1, d.2.1, d.2.2.2.1)) hunion g2.computableIn
  have k3 : IsREIn B fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      G.φ (d.2.1 : ℝ) (E.secPt d.1.1 d.1.2) ∈ basicBall P d.2.2.2.2 :=
    IsREIn.comp (f := fun d : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ↦
      (d.1, d.2.1, d.2.2.2.2)) hball g3.computableIn
  obtain ⟨f, hf, hdom⟩ := (k1.and k2).and k3
  refine ⟨f, hf, fun d ↦ Iff.trans ?_ (hdom d)⟩
  simp only [Set.mem_inter_iff]

/-- The rounding test of the search: the shifted section point lies in a basic ball whose
rational radius is below the requested precision. Blueprint node `geo:section-reconstruction`. -/
private theorem isREIn_shift_round :
    IsREIn B fun e : ((Fin G.nBoxes × ℕ) × ℚ × ℚ) × (ℕ × ℚ) ↦
      G.φ (e.1.2.1 : ℝ) (E.secPt e.1.1.1 e.1.1.2) ∈ basicBall P e.2 ∧ e.2.2 < e.1.2.2 := by
  have hg : Computable fun e : ((Fin G.nBoxes × ℕ) × ℚ × ℚ) × (ℕ × ℚ) ↦
      (e.1.1, e.1.2.1, e.2) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
  have h1 : IsREIn B fun e : ((Fin G.nBoxes × ℕ) × ℚ × ℚ) × (ℕ × ℚ) ↦
      G.φ (e.1.2.1 : ℝ) (E.secPt e.1.1.1 e.1.1.2) ∈ basicBall P e.2 :=
    IsREIn.comp (f := fun e : ((Fin G.nBoxes × ℕ) × ℚ × ℚ) × (ℕ × ℚ) ↦ (e.1.1, e.1.2.1, e.2))
      E.isREIn_shift_mem_basicBall hg.computableIn
  have h2 : IsREIn B fun e : ((Fin G.nBoxes × ℕ) × ℚ × ℚ) × (ℕ × ℚ) ↦ e.2.2 < e.1.2.2 :=
    isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.snd.comp Computable.snd)
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  exact h1.and h2

/-! ### `geo:section-localization` -/

omit E in
/-- Integral localization on a shifted section (OTL `cor:integral_section_localization`). Given
the neighborhoods of Chapter F with their containments, the coded neighborhood `V'` of the
shifted transverse estimate, a time shift `s` with `w = φ (-s) x` in the box and a local time
`|τ w| < ε_x` below the target plaque radius, the section point `z = φ s (proj w) = φ (τ w) x`
lies in `Ω = U^{cs} ∩ U^{cu} ∩ φ s '' D ∩ V'` (by `dW_cs_flow_self`, `dW_cu_flow_self`), and
every `y ∈ Ω` satisfies `dist y z ≤ Ltr C₂ max (E₊(ρ), E₋(ρ))`.
Blueprint node `geo:section-localization`. -/
theorem section_localization (x : X) (hx : x ∈ G.Reg) {j : Fin G.nBoxes} {s : ℝ}
    (hxj : G.φ (-s) x ∈ (G.box j).U) {εx : ℝ} (_hε : 0 < εx)
    (hτ : |(G.box j).τ (G.φ (-s) x)| < εx) {V' : Set X}
    (hzV : G.φ s ((G.box j).proj (G.φ (-s) x)) ∈ V') {Ltr : ℝ} (hLtr : 0 ≤ Ltr)
    (htr : ∀ y ∈ G.φ s '' (G.box j).D ∩ V', dist y (G.φ s ((G.box j).proj (G.φ (-s) x))) ≤
      Ltr * max (Metric.infDist y (G.Wloc .cs x)) (Metric.infDist y (G.Wloc .cu x)))
    {Ucs Ucu : Set X} {C₂ sp sm : ℝ} (hC₂ : 0 ≤ C₂) (_hsp : 0 ≤ sp) (_hsm : 0 ≤ sm)
    (h1 : G.plaque .cs εx x ⊆ Ucs) (h2 : Ucs ⊆ Metric.thickening (C₂ * sp) (G.Wloc .cs x))
    (h3 : G.plaque .cu εx x ⊆ Ucu) (h4 : Ucu ⊆ Metric.thickening (C₂ * sm) (G.Wloc .cu x)) :
    G.φ s ((G.box j).proj (G.φ (-s) x)) ∈ Ucs ∩ Ucu ∩ G.φ s '' (G.box j).D ∩ V' ∧
      ∀ y ∈ Ucs ∩ Ucu ∩ G.φ s '' (G.box j).D ∩ V',
        dist y (G.φ s ((G.box j).proj (G.φ (-s) x))) ≤ Ltr * C₂ * max sp sm := by
  have _ := hx
  -- the section point is the time shift `φ (τ w) x` of `x`
  have hz_eq : G.φ s ((G.box j).proj (G.φ (-s) x)) = G.φ ((G.box j).τ (G.φ (-s) x)) x := by
    unfold FlowBox.proj
    rw [← Flow.map_add, ← Flow.map_add]
    congr 1
    ring
  have hz1 : G.φ s ((G.box j).proj (G.φ (-s) x)) ∈ G.plaque .cs εx x := by
    rw [hz_eq]
    refine ⟨?_, (G.dW_cs_flow_self x _).trans_lt hτ⟩
    rw [G.W_cs_eq]
    exact Set.mem_iUnion.mpr ⟨_, x, G.mem_W .s x, rfl⟩
  have hz2 : G.φ s ((G.box j).proj (G.φ (-s) x)) ∈ G.plaque .cu εx x := by
    rw [hz_eq]
    refine ⟨?_, (G.dW_cu_flow_self x _).trans_lt hτ⟩
    rw [G.W_cu_eq]
    exact Set.mem_iUnion.mpr ⟨_, x, G.mem_W .u x, rfl⟩
  have hzD : G.φ s ((G.box j).proj (G.φ (-s) x)) ∈ G.φ s '' (G.box j).D :=
    ⟨_, (G.proj_spec hxj).1, rfl⟩
  refine ⟨⟨⟨⟨h1 hz1, h3 hz2⟩, hzD⟩, hzV⟩, fun y hy ↦ ?_⟩
  obtain ⟨⟨⟨hy1, hy2⟩, hyD⟩, hyV⟩ := hy
  obtain ⟨z₁, hz₁, hd₁⟩ := Metric.mem_thickening_iff.mp (h2 hy1)
  obtain ⟨z₂, hz₂, hd₂⟩ := Metric.mem_thickening_iff.mp (h4 hy2)
  have i1 : Metric.infDist y (G.Wloc .cs x) ≤ C₂ * sp :=
    (Metric.infDist_le_dist_of_mem hz₁).trans hd₁.le
  have i2 : Metric.infDist y (G.Wloc .cu x) ≤ C₂ * sm :=
    (Metric.infDist_le_dist_of_mem hz₂).trans hd₂.le
  calc dist y (G.φ s ((G.box j).proj (G.φ (-s) x)))
      ≤ Ltr * max (Metric.infDist y (G.Wloc .cs x)) (Metric.infDist y (G.Wloc .cu x)) :=
        htr y ⟨hyD, hyV⟩
    _ ≤ Ltr * max (C₂ * sp) (C₂ * sm) := mul_le_mul_of_nonneg_left (max_le_max i1 i2) hLtr
    _ = Ltr * C₂ * max sp sm := by rw [mul_assoc, mul_max_of_nonneg _ _ hC₂]

/-- `Ω` is relatively open in the shifted section and contains `z`, so the shifted dense sequence
`φ s (secPt j k)` meets it: the search of `geo:section-reconstruction` terminates.
Blueprint node `geo:section-localization`. -/
theorem exists_secPt_mem {j : Fin G.nBoxes} {s : ℝ} {O : Set X} (hO : IsOpen O) {z : X}
    (hz : z ∈ G.φ s '' (G.box j).D) (hzO : z ∈ O) :
    ∃ k, G.φ s (E.secPt j k) ∈ O := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hcont : Continuous fun y : X ↦ G.φ s y := G.φ.continuous continuous_const continuous_id
  obtain ⟨y, hyO, k, rfl⟩ := mem_closure_iff_nhds.mp (E.secPt_dense j hw) _
    ((hO.preimage hcont).mem_nhds hzO)
  exact ⟨k, hyO⟩

/-! ### `geo:section-reconstruction` -/

/-- Effective reconstruction on a shifted section (OTL `cor:integral_point_reconstruction`). For
compact regular endpoint sets and a rational loss `ρ` there are a tolerance `ε`, a plaque
threshold `ε₀`, a compact neighborhood `Q` of the endpoint sets, and one `B`-partial recursive
program `recon` such that, when the compact plaques over `Q` are `ε₀`-small: every regular `x`
has localization data (a box `j`, a rational time shift `s` with `w = φ (-s) x` in the box, a
neighborhood code `(c, rV)`, a radius `r`) and a constant `C₃` such that for regular endpoints
`φ Tp x ∈ Pp`, `φ (-Tm) x ∈ Pm` and orbit data `dp, dm` of orders `Tp + 1`, `Tm + 1` at
tolerance at most `min ε (r/8)`, the program halts on `(j, s, c, rV, dp.idx, dm.idx, Tp, Tm, r)`
with an ideal index within `C₃ max (E₊(ρ), E₋(ρ))` of the shifted section point
`z = φ s (proj w) = φ (τ w) x`.
The program runs `effective_neighborhoods`, searches the shifted sequence `φ s (secPt j k)` for a
point certified in `U^{cs} ∩ U^{cu} ∩ basicBall (c', rV)` together with a basic ball of radius
below `max (Rp, Rm)` containing it (`isREIn_secPt_mem`, `isREIn_shift_round`, enumerated by
`relative_enumeration`; terminating by `exists_secPt_mem`), bounds the distance to `z` by
`section_localization`, and outputs the center of that ball; so `C₃ = Ltr C₂ + 1`. The shift `s`
is chosen so close to `-τ x` that `|τ w| < ε_x` (continuity of `τ`, `τ (proj x) = 0`). The base
points range over a compact regular set `Px` (needed by the decoders of Chapter E). The
localization data and `C₃` do not depend on the durations.
Blueprint node `geo:section-reconstruction`. -/
theorem section_reconstruction {Pp Pm : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (hPm : IsCompact Pm) (hPmR : Pm ⊆ G.Reg) {Px : Set X} (hPx : IsCompact Px)
    (hPxR : Px ⊆ G.Reg) (ρ : ℚ) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Q : Set X, IsCompact Q ∧
      Pp ∪ Pm ⊆ interior Q ∧ Q ⊆ G.Reg ∧
      ∃ recon : Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ →. ℕ,
        PartrecIn {charOracle B} recon ∧
        (G.SmallPlaques Q ε₀ →
          ∀ x ∈ Px, ∃ (j : Fin G.nBoxes) (s : ℚ) (c : ℕ) (rV r : ℚ) (C₃ : ℝ),
            G.φ (-(s : ℝ)) x ∈ (G.box j).U ∧ 0 < r ∧ 0 < C₃ ∧
            ∀ Tp Tm : ℕ, G.φ (Tp : ℝ) x ∈ Pp → G.φ (-(Tm : ℝ)) x ∈ Pm →
            ∀ (dp : OrbitDatum P G.f x) (dm : OrbitDatum P G.finv x),
              dp.order = Tp + 1 → dp.tol ≤ min ε (r / 8) →
              dm.order = Tm + 1 → dm.tol ≤ min ε (r / 8) →
              (recon (j, s, c, rV, dp.idx, dm.idx, Tp, Tm, r)).Dom ∧
                ∀ q ∈ recon (j, s, c, rV, dp.idx, dm.idx, Tp, Tm, r),
                  dist (P.ι q) (G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x))) ≤
                    C₃ * max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x)) := by
  obtain ⟨ε, hε, C₂, hC₂, ε₀, hε₀, Q, hQ, hPQ, hQR, nbhd, hnbhd, hspec⟩ :=
    E.effective_neighborhoods hPp hPpR hPm hPmR hPx hPxR ρ hρ
  -- the search predicate on the witnesses `((j, k), s, L₁, L₂, b₀, δ, c)`
  have hF : IsREIn B fun w : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) ×
      ℚ × (ℕ × ℚ) ↦
      (G.φ (w.2.1 : ℝ) (E.secPt w.1.1 w.1.2) ∈
        ballUnion P w.2.2.1 ∩ ballUnion P w.2.2.2.1 ∩ basicBall P w.2.2.2.2.1) ∧
      (G.φ (w.2.1 : ℝ) (E.secPt w.1.1 w.1.2) ∈ basicBall P w.2.2.2.2.2.2 ∧
        w.2.2.2.2.2.2.2 < w.2.2.2.2.2.1) := by
    have hg1 : Computable fun w : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) ×
        (ℕ × ℚ) × ℚ × (ℕ × ℚ) ↦ (w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1) :=
      Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
            (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
              (Computable.snd.comp Computable.snd)))))))
    have hg2 : Computable fun w : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) ×
        (ℕ × ℚ) × ℚ × (ℕ × ℚ) ↦ ((w.1, w.2.1, w.2.2.2.2.2.1), w.2.2.2.2.2.2) :=
      (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.snd.comp Computable.snd))))))).pair
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
          (Computable.snd.comp Computable.snd)))))
    exact (IsREIn.comp (f := fun w : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) ×
        (ℕ × ℚ) × ℚ × (ℕ × ℚ) ↦ (w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1))
        E.isREIn_secPt_mem hg1.computableIn).and
      (IsREIn.comp (f := fun w : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) ×
        (ℕ × ℚ) × ℚ × (ℕ × ℚ) ↦ ((w.1, w.2.1, w.2.2.2.2.2.1), w.2.2.2.2.2.2))
        E.isREIn_shift_round hg2.computableIn)
  obtain ⟨e, he, henum⟩ := (relative_enumeration B _).mp hF
  -- the search step: scan the enumeration for a witness with the given key
  obtain ⟨key, hkey_def⟩ : ∃ key : (Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) ×
      (ℕ × ℚ) × ℚ × (ℕ × ℚ) →
        (Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) × ((ℕ × ℚ) × ℚ),
      key = fun w ↦ ((w.1.1, w.2.1), (w.2.2.1, w.2.2.2.1), (w.2.2.2.2.1, w.2.2.2.2.2.1)) :=
    ⟨_, rfl⟩
  have hkey : Primrec key := by
    rw [hkey_def]
    exact ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
      (((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd)))).pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.snd)))))))
  obtain ⟨step, hstep_def⟩ : ∃ step : ((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
      ((ℕ × ℚ) × ℚ)) × ℕ → Option ℕ, step = fun kt ↦ (e kt.2).bind fun w ↦
        if key w = kt.1 then some w.2.2.2.2.2.2.1 else none := ⟨_, rfl⟩
  have hstep : ComputableIn {charOracle B} step := by
    rw [hstep_def]
    have hg : Primrec fun p : (((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
        ((ℕ × ℚ) × ℚ)) ×
        Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ))) ×
        ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
        if key p.2 = p.1.1 then some p.2.2.2.2.2.2.2.1 else none := by
      have : DecidablePred fun p : (((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
          ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ))) ×
          ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
          key p.2 = p.1.1 := fun _ ↦ inferInstance
      have q1 : Primrec fun p : (((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
          ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ))) ×
          ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
          p.1.1 := Primrec.fst.comp Primrec.fst
      have q2 : Primrec fun p : (((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
          ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ))) ×
          ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
          p.2 := Primrec.snd
      have q3 : Primrec fun p : (((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
          ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ))) ×
          ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
          p.2.2.2.2.2.2.2.1 :=
        Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
      have hc : PrimrecPred fun p : (((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
          ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ))) ×
          ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
          key p.2 = p.1.1 := Primrec.eq.comp (hkey.comp q2) q1
      exact (Primrec.ite hc (Primrec.option_some.comp q3) (Primrec.const none)).of_eq
        fun _ ↦ by congr
    have h0 : Computable fun q : ((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) ×
        ((ℕ × ℚ) × ℚ)) ×
        Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ × (ℕ × ℚ)) ↦
        q.2.bind fun w ↦ if key w = q.1 then some w.2.2.2.2.2.2.1 else none :=
      Computable.option_bind
        (f := fun q : ((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) × ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ)) ↦ q.2)
        (g := fun (q : ((Fin G.nBoxes × ℚ) × (List (ℕ × ℚ) × List (ℕ × ℚ)) × ((ℕ × ℚ) × ℚ)) ×
          Option ((Fin G.nBoxes × ℕ) × ℚ × List (ℕ × ℚ) × List (ℕ × ℚ) × (ℕ × ℚ) × ℚ ×
            (ℕ × ℚ))) w ↦ if key w = q.1 then some w.2.2.2.2.2.2.1 else none)
        Computable.snd hg.to_comp
    exact (h0.computableIn.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd))).of_eq
      fun _ ↦ rfl
  -- rational maximum
  have hmaxq : Computable₂ fun a b : ℚ ↦ max a b := by
    have h : Computable fun p : ℚ × ℚ ↦ bif decide (p.1 < p.2) then p.2 else p.1 :=
      Computable.cond (computable₂_ratLt.comp Computable.fst Computable.snd) Computable.snd
        Computable.fst
    refine h.of_eq fun p ↦ ?_
    rcases lt_or_ge p.1 p.2 with h | h
    · simp [h, max_eq_right h.le]
    · simp [not_lt.mpr h, max_eq_left h]
  -- the program
  obtain ⟨recon, hrecon_def⟩ : ∃ recon : Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ →. ℕ,
      recon = fun d ↦
        (nbhd (d.1, d.2.2.2.2.1, d.2.2.2.2.2.1, d.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.1,
          d.2.2.2.2.2.2.2.2)).bind fun out ↦
          Nat.rfindOpt fun t ↦ step (((d.1, d.2.1), (out.1, out.2.1),
            ((d.2.2.1, d.2.2.2.1), max out.2.2.1 out.2.2.2)), t) := ⟨_, rfl⟩
  have hrecon : PartrecIn {charOracle B} recon := by
    rw [hrecon_def]
    have hnb : PartrecIn {charOracle B}
        fun d : Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ ↦
          nbhd (d.1, d.2.2.2.2.1, d.2.2.2.2.2.1, d.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.1,
            d.2.2.2.2.2.2.2.2) := by
      have hg : Computable fun d : Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ ↦
          (d.1, d.2.2.2.2.1, d.2.2.2.2.2.1, d.2.2.2.2.2.2.1, d.2.2.2.2.2.2.2.1,
            d.2.2.2.2.2.2.2.2) := by
        have s4 : Computable fun d : Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ ↦
            d.2.2.2.2 :=
          Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
        exact Computable.fst.pair ((Computable.fst.comp s4).pair
          ((Computable.fst.comp (Computable.snd.comp s4)).pair
            ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp s4))).pair
              ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
                (Computable.snd.comp s4)))).pair
                (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
                  (Computable.snd.comp s4))))))))
      exact hnbhd.comp hg.computableIn
    have hsearch : PartrecIn {charOracle B}
        fun p : (Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ) ×
          (List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ) ↦
          Nat.rfindOpt fun t ↦ step (((p.1.1, p.1.2.1), (p.2.1, p.2.2.1),
            ((p.1.2.2.1, p.1.2.2.2.1), max p.2.2.2.1 p.2.2.2.2)), t) := by
      have hk : Computable fun p : (Fin G.nBoxes × ℚ × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ × ℚ) ×
          (List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ) ↦
          ((p.1.1, p.1.2.1), (p.2.1, p.2.2.1),
            ((p.1.2.2.1, p.1.2.2.2.1), max p.2.2.2.1 p.2.2.2.2)) := by
        exact ((Computable.fst.comp Computable.fst).pair
          (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
          (((Computable.fst.comp Computable.snd).pair
            (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
            (((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair
              (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
                (Computable.snd.comp Computable.fst))))).pair
              (hmaxq.comp (Computable.fst.comp (Computable.snd.comp
                (Computable.snd.comp Computable.snd)))
                (Computable.snd.comp (Computable.snd.comp
                  (Computable.snd.comp Computable.snd))))))
      refine PartrecIn.rfindOpt (ComputableIn₂.mk ?_)
      exact (hstep.comp (hk.computableIn.comp ComputableIn.fst |>.pair ComputableIn.snd)).of_eq
        fun _ ↦ rfl
    exact PartrecIn.bind hnb (PartrecIn.to₂ hsearch)
  refine ⟨ε, hε, ε₀, hε₀, Q, hQ, hPQ, hQR, recon, hrecon, fun hsmall x hx ↦ ?_⟩
  have hxR : x ∈ G.Reg := hPxR hx
  obtain ⟨j, r, εx, hxj, hr, hεx, hnb⟩ := hspec hsmall x hx
  -- the time shift: a rational `s` close to `-τ x`
  have hw₀D := (G.proj_spec hxj).1
  have hw₀U : (G.box j).proj x ∈ (G.box j).U := (G.box j).D_subset hw₀D
  have hτw₀ : (G.box j).τ ((G.box j).proj x) = 0 :=
    ((G.box j).τ_unique _ hw₀U 0 (by rw [abs_zero]; exact (G.box j).a_pos)
      (by rw [Flow.map_zero_apply]; exact hw₀D)).symm
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.mp (G.box j).isOpen_U _ hw₀U
  obtain ⟨δ₂, hδ₂, hδ₂τ⟩ := Metric.continuousOn_iff.mp (G.box j).continuousOn_τ _ hw₀U εx hεx
  have hcont : Continuous fun t : ℝ ↦ G.φ (-t) x := G.φ.continuous continuous_neg continuous_const
  obtain ⟨η, hη, hηs⟩ := Metric.continuous_iff.mp hcont (-(G.box j).τ x) (min δ₁ δ₂)
    (lt_min hδ₁ hδ₂)
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (sub_lt_self (-(G.box j).τ x) hη)
  have hws : dist (G.φ (-(s : ℝ)) x) ((G.box j).proj x) < min δ₁ δ₂ := by
    have h := hηs s (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simpa only [neg_neg, FlowBox.proj] using h
  have hwU : G.φ (-(s : ℝ)) x ∈ (G.box j).U :=
    hδ₁U (Metric.mem_ball.mpr (hws.trans_le (min_le_left _ _)))
  have hτw : |(G.box j).τ (G.φ (-(s : ℝ)) x)| < εx := by
    have := hδ₂τ _ hwU (hws.trans_le (min_le_right _ _))
    rwa [hτw₀, Real.dist_eq, sub_zero] at this
  -- the shifted transverse estimate and its coded neighborhood
  obtain ⟨V, hV, hzV, Ltr, hLtr, htr⟩ := G.transverse_estimate x hxR j s hwU
  obtain ⟨c', rV, hrV, hzV', hV'⟩ := exists_basicBall_code (P := P) hV hzV
  have htr' : ∀ y ∈ G.φ (s : ℝ) '' (G.box j).D ∩ basicBall P (c', rV),
      dist y (G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x))) ≤
        Ltr * max (Metric.infDist y (G.Wloc .cs x)) (Metric.infDist y (G.Wloc .cu x)) :=
    fun y hy ↦ htr y ⟨hy.1, hV' hy.2⟩
  refine ⟨j, s, c', rV, r, Ltr * C₂ + 1, hwU, hr, by positivity,
    fun Tp Tm hTp hTm dp dm hdpT hdptol hdmT hdmtol ↦ ?_⟩
  have hip := dp.mem_order hdpT hdptol
  have him := dm.mem_order hdmT hdmtol
  generalize dp.idx = ip at hip ⊢
  generalize dm.idx = im at him ⊢
  obtain ⟨hdom, hout⟩ := hnb Tp Tm hTp hTm (OrbitDatum.ofMem hip) (OrbitDatum.ofMem him)
    rfl le_rfl rfl le_rfl
  simp only [OrbitDatum.ofMem_idx] at hdom hout
  rw [hrecon_def]
  dsimp only
  -- the open set searched
  have hΩopen : ∀ out : List (ℕ × ℚ) × List (ℕ × ℚ) × ℚ × ℚ,
      IsOpen (ballUnion P out.1 ∩ ballUnion P out.2.1 ∩ basicBall P (c', rV)) := by
    intro out
    refine (IsOpen.inter (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball)
      (isOpen_biUnion fun _ _ ↦ Metric.isOpen_ball)).inter Metric.isOpen_ball
  -- the properties of a certified witness
  have hmax : ∀ out ∈ nbhd (j, ip, im, Tp, Tm, r),
      (max out.2.2.1 out.2.2.2 : ℝ) ≤ max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) := by
    intro out hmem
    obtain ⟨-, -, -, -, -, -, h5, -, -, h6⟩ := hout out hmem
    exact max_le_max h5 h6
  have hloc : ∀ out ∈ nbhd (j, ip, im, Tp, Tm, r),
      G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x)) ∈
        ballUnion P out.1 ∩ ballUnion P out.2.1 ∩ G.φ (s : ℝ) '' (G.box j).D ∩
          basicBall P (c', rV) ∧
      ∀ y ∈ ballUnion P out.1 ∩ ballUnion P out.2.1 ∩ G.φ (s : ℝ) '' (G.box j).D ∩
          basicBall P (c', rV),
        dist y (G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x))) ≤
          Ltr * C₂ * max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) := by
    intro out hmem
    obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -⟩ := hout out hmem
    exact section_localization x hxR hwU hεx hτw hzV' hLtr.le htr' hC₂.le
      (G.scalePlus_pos _ _ _).le (G.scaleMinus_pos _ _ _).le h1 h2 h3 h4
  -- a certified witness exists: termination
  have hwit : ∀ out ∈ nbhd (j, ip, im, Tp, Tm, r), ∃ t, ∃ q,
      q ∈ step (((j, s), (out.1, out.2.1), ((c', rV), max out.2.2.1 out.2.2.2)), t) := by
    intro out hmem
    obtain ⟨hz, -⟩ := hloc out hmem
    obtain ⟨-, -, -, -, hRp0, -, -, -, -, -⟩ := hout out hmem
    have hzΩ : G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x)) ∈
        ballUnion P out.1 ∩ ballUnion P out.2.1 ∩ basicBall P (c', rV) :=
      ⟨hz.1.1, hz.2⟩
    obtain ⟨k, hk⟩ := E.exists_secPt_mem (hΩopen out) hz.1.2 hzΩ
    have hδ : (0 : ℚ) < max out.2.2.1 out.2.2.2 := lt_max_of_lt_left hRp0
    have hδ' : (0 : ℝ) < ((max out.2.2.1 out.2.2.2 : ℚ) : ℝ) := by exact_mod_cast hδ
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.mp P.dense (G.φ (s : ℝ) (E.secPt j k))
      (((max out.2.2.1 out.2.2.2 : ℚ) : ℝ) / 2) (by positivity)
    obtain ⟨rc, hrc1, hrc2⟩ := exists_rat_btwn (half_lt_self hδ')
    have hFw : (G.φ (s : ℝ) (E.secPt j k) ∈
          ballUnion P out.1 ∩ ballUnion P out.2.1 ∩ basicBall P (c', rV)) ∧
        (G.φ (s : ℝ) (E.secPt j k) ∈ basicBall P (m, rc) ∧ rc < max out.2.2.1 out.2.2.2) := by
      refine ⟨hk, ?_, by exact_mod_cast hrc2⟩
      change G.φ (s : ℝ) (E.secPt j k) ∈ Metric.ball (P.ι m) (rc : ℝ)
      exact Metric.mem_ball.mpr (hm.trans hrc1)
    obtain ⟨t, ht⟩ := (henum ((j, k), s, out.1, out.2.1, (c', rV), max out.2.2.1 out.2.2.2,
      (m, rc))).mp hFw
    refine ⟨t, m, ?_⟩
    rw [hstep_def]
    dsimp only
    rw [ht, Option.bind_some, hkey_def]
    simp
  -- the output of a certified witness is close to the section point
  have hval : ∀ out ∈ nbhd (j, ip, im, Tp, Tm, r), ∀ t q,
      q ∈ step (((j, s), (out.1, out.2.1), ((c', rV), max out.2.2.1 out.2.2.2)), t) →
      dist (P.ι q) (G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x))) ≤
        (Ltr * C₂ + 1) * max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) := by
    intro out hmem t q hq
    rw [hstep_def] at hq
    dsimp only at hq
    rw [Option.mem_def, Option.bind_eq_some_iff] at hq
    obtain ⟨w, hw, hqw⟩ := hq
    by_cases hkw : key w = ((j, s), (out.1, out.2.1), ((c', rV), max out.2.2.1 out.2.2.2))
    swap
    · simp [hkw] at hqw
    simp only [hkw, ite_true, Option.some_inj] at hqw
    subst hqw
    rw [hkey_def] at hkw
    simp only [Prod.mk.injEq] at hkw
    obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩, hw5, hw6⟩ := hkw
    have hFw := (henum w).mpr ⟨t, hw⟩
    obtain ⟨hmemΩ, hball, hrad⟩ := hFw
    rw [hw2, hw3, hw4, hw5] at hmemΩ
    rw [hw2] at hball
    rw [hw6] at hrad
    have hyD : G.φ (s : ℝ) (E.secPt w.1.1 w.1.2) ∈ G.φ (s : ℝ) '' (G.box j).D :=
      ⟨E.secPt w.1.1 w.1.2, by rw [hw1]; exact E.secPt_mem _ _, rfl⟩
    have hdist := (hloc out hmem).2 _ ⟨⟨hmemΩ.1, hyD⟩, hmemΩ.2⟩
    have hball' : dist (G.φ (s : ℝ) (E.secPt w.1.1 w.1.2)) (P.ι w.2.2.2.2.2.2.1) <
        (w.2.2.2.2.2.2.2 : ℝ) := Metric.mem_ball.mp hball
    have hrad' : (w.2.2.2.2.2.2.2 : ℝ) < ((max out.2.2.1 out.2.2.2 : ℚ) : ℝ) := by
      exact_mod_cast hrad
    have hmax' := hmax out hmem
    push_cast at hrad' hmax'
    calc dist (P.ι w.2.2.2.2.2.2.1) (G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x)))
        ≤ dist (P.ι w.2.2.2.2.2.2.1) (G.φ (s : ℝ) (E.secPt w.1.1 w.1.2)) +
          dist (G.φ (s : ℝ) (E.secPt w.1.1 w.1.2))
            (G.φ (s : ℝ) ((G.box j).proj (G.φ (-(s : ℝ)) x))) := dist_triangle _ _ _
      _ ≤ max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) +
          Ltr * C₂ * max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) := by
          rw [dist_comm]
          linarith
      _ = (Ltr * C₂ + 1) * max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) := by ring
  constructor
  · rw [Part.bind_dom]
    refine ⟨hdom, ?_⟩
    obtain ⟨t, q, hq⟩ := hwit _ (Part.get_mem hdom)
    exact Nat.rfindOpt_dom.mpr ⟨t, q, hq⟩
  · intro q hq
    obtain ⟨out, hmem, hq'⟩ := Part.mem_bind_iff.mp hq
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hq'
    exact hval out hmem t q ht

omit E in
/-- The combined scale as a single exponential:
`max (E₊(ρ), E₋(ρ)) = 2 ^ (-min (S_Tp u⁺(x) - ρ Tp, S_Tm u⁻(x) - ρ Tm))`, the quantity
`𝓡_ρ(x; T⁺, T⁻)` of OTL `eq:combined-scale`. Blueprint node `geo:section-reconstruction`. -/
theorem max_scale_eq (ρ : ℝ) (Tp Tm : ℕ) (x : X) :
    max (G.scalePlus ρ Tp x) (G.scaleMinus ρ Tm x) =
      (2 : ℝ) ^ (-min (birkhoffSum G.f G.uPlus Tp x - ρ * Tp)
        (birkhoffSum G.finv G.uMinus Tm x - ρ * Tm)) := by
  have hmono : Monotone fun t : ℝ ↦ (2 : ℝ) ^ t :=
    fun _ _ h ↦ Real.rpow_le_rpow_of_exponent_le one_le_two h
  unfold GeodesicReconstructionData.scalePlus GeodesicReconstructionData.scaleMinus
  rw [← max_neg_neg]
  exact (hmono.map_max).symm

end EffectiveGeodesicData

end Kolmogorov.PointToSet
