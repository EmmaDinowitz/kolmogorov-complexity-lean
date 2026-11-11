/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.CeOpen
import KolmogorovMathlib.Oracle.Search

/-!
# Represented families and maps represented on a subset

Two variants of the library's represented maps (`IsRepresentedMapIn`). A family of maps indexed
by a primcodable type is represented uniformly by one enumerable sound ball relation tagged by
the index (`IsRepresentedFamilyIn`); each member is a represented map, the family evaluates
computable points to computable points uniformly in the index, and preimages of c.e. open
families under it are c.e. open (`IsRepresentedFamilyIn.preimage_ceOpen`). A map is represented
on a subset `S` when soundness and completeness are only required on `S`
(`IsRepresentedOnIn`), which is what maps continuous only on an open set provide; such a map
sends computable points of `S` to computable points. The core of both evaluation lemmas is
`exists_names_of_ballRel_uniform`, a dovetailed search for a small listed ball about the image.
Blueprint nodes `eff:represented-on`, `eff:represented-family`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A family of maps indexed by a primcodable type is represented uniformly: one enumerable
sound relation between basic balls, tagged by the index, complete at every point of every
member. Blueprint node `geo:effective-data` (item 2). -/
def IsRepresentedFamilyIn {ι : Type*} [Primcodable ι] (P : Presentation X) (Q : Presentation Y)
    (A : Set ℕ) (f : ι → X → Y) : Prop :=
  ∃ R : ι × (ℕ × ℚ) × (ℕ × ℚ) → Prop, IsREIn A R ∧
    (∀ i b c, R (i, b, c) → 0 < b.2 ∧ 0 < c.2 ∧ f i '' basicBall P b ⊆ basicBall Q c) ∧
    ∀ i x c, f i x ∈ basicBall Q c → ∃ b, R (i, b, c) ∧ x ∈ basicBall P b

/-- A map is represented on a subset `S`: soundness is required only for the part of each
basic ball inside `S`, completeness only at points of `S`.
Blueprint node `geo:effective-data` (item 5). -/
def IsRepresentedOnIn (P : Presentation X) (Q : Presentation Y) (A : Set ℕ) (S : Set X)
    (f : X → Y) : Prop :=
  ∃ R : (ℕ × ℚ) × (ℕ × ℚ) → Prop, IsREIn A R ∧
    (∀ b c, R (b, c) → 0 < b.2 ∧ 0 < c.2 ∧ f '' (basicBall P b ∩ S) ⊆ basicBall Q c) ∧
    ∀ x ∈ S, ∀ c, f x ∈ basicBall Q c → ∃ b, R (b, c) ∧ x ∈ basicBall P b

section aux

variable {P : Presentation X} {Q : Presentation Y} {A B : Set ℕ}

/-- Represented maps transfer to every Turing-stronger oracle. -/
theorem isRepresentedMapIn_mono_oracle {f : X → Y} (hf : IsRepresentedMapIn P Q A f)
    (hAB : charOracle A ≤ᵀ charOracle B) : IsRepresentedMapIn P Q B f := by
  obtain ⟨R, hR, hs, hc⟩ := hf
  exact ⟨R, hR.mono_oracle hAB, hs, hc⟩

/-- A map continuous at `x` sends some positive basic ball about `x` into any basic ball about
`f x`; the pair of balls is sound. -/
theorem exists_basicBall_image_subset_of_continuousAt {f : X → Y} {x : X}
    (hf : ContinuousAt f x) {c : ℕ × ℚ} (hx : f x ∈ basicBall Q c) :
    ∃ b : ℕ × ℚ, (0 < b.2 ∧ 0 < c.2 ∧ f '' basicBall P b ⊆ basicBall Q c) ∧ x ∈ basicBall P b := by
  have hx' : dist (Q.ι c.1) (f x) < (c.2 : ℝ) := Metric.mem_ball'.mp hx
  have hc : (0 : ℚ) < c.2 := by exact_mod_cast dist_nonneg.trans_lt hx'
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (hf.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hx))
  obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense x (ε / 4) (by positivity)
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  have hk' : dist (P.ι k) x < ε / 4 := by
    rw [dist_comm]
    exact hk
  refine ⟨(k, q), ⟨?_, hc, ?_⟩, Metric.mem_ball.mpr (hk.trans hq₁)⟩
  · exact_mod_cast (show (0 : ℝ) < ε / 4 by positivity).trans hq₁
  · rintro _ ⟨z, hz, rfl⟩
    refine hεsub (Metric.mem_ball.mpr ?_)
    have hz' : dist z (P.ι k) < q := hz
    calc dist z x ≤ dist z (P.ι k) + dist (P.ι k) x := dist_triangle _ _ _
      _ < q + ε / 4 := add_lt_add hz' hk'
      _ < ε := by linarith

/-- Core of the evaluation lemmas, uniform in the point: an enumerable family of ball pairs that
is sound and complete at the points `x i` (with uniformly computable names) yields computable
names of the images `y i`, uniformly in the index. -/
theorem exists_names_of_ballRel_uniform {ι : Type*} [Primcodable ι]
    (hP : ComputablePresentationIn P A)
    {R : ι × (ℕ × ℚ) × (ℕ × ℚ) → Prop} (hR : IsREIn A R) {y : ι → Y} {x : ι → X}
    (hsound : ∀ i b c, R (i, b, c) → x i ∈ basicBall P b → y i ∈ basicBall Q c)
    (hcomplete : ∀ i c, y i ∈ basicBall Q c → ∃ b, R (i, b, c) ∧ x i ∈ basicBall P b)
    {a : ι → ℕ → ℕ} (ha : ∀ i, IsCauchyName P (x i) (a i))
    (hcomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 ip.2) :
    ∃ b : ι → ℕ → ℕ, ComputableIn {charOracle A} (fun ip : ι × ℕ ↦ b ip.1 ip.2) ∧
      ∀ i, IsCauchyName Q (y i) (b i) := by
  let Good : (ι × ℕ) × (ℕ × ℚ) → Prop := fun w ↦
    ((0 : ℚ) < w.2.2 ∧ w.2.2 < (2 ^ w.1.2 : ℚ)⁻¹) ∧
      ∃ b, R (w.1.1, b, w.2) ∧ x w.1.1 ∈ basicBall P b
  have hGood : IsREIn A Good := by
    have hpos : IsREIn A fun w : (ι × ℕ) × (ℕ × ℚ) ↦ (0 : ℚ) < w.2.2 :=
      isREIn_of_computable_decide
        (computable₂_ratLt.comp (Computable.const 0) (Computable.snd.comp Computable.snd))
    have hsmall : IsREIn A fun w : (ι × ℕ) × (ℕ × ℚ) ↦ w.2.2 < (2 ^ w.1.2 : ℚ)⁻¹ :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.snd.comp Computable.snd)
        (computable_rat_inv_two_pow.comp (Computable.snd.comp Computable.fst)))
    have hrel : IsREIn A fun wb : ((ι × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        R (wb.1.1.1, wb.2, wb.1.2) ∧ x wb.1.1.1 ∈ basicBall P wb.2 :=
      (hR.comp (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        (Computable.snd.pair (Computable.snd.comp Computable.fst))).computableIn)).and
        ((isREIn_mem_basicBall_of_names hP ha hcomp).comp
          ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
            Computable.snd).computableIn)
    exact (hpos.and hsmall).and hrel.exists
  have htot : ∀ ip : ι × ℕ, ∃ c, Good (ip, c) := by
    rintro ⟨i, p⟩
    obtain ⟨c, hc, hcpos, hcsmall⟩ := exists_mem_basicBall_radius_lt Q (y i) p
    obtain ⟨b, hb, hxb⟩ := hcomplete i c hc
    exact ⟨c, ⟨hcpos, hcsmall⟩, b, hb, hxb⟩
  obtain ⟨g, hg, hgood⟩ := hGood.exists_computableIn_choice htot
  refine ⟨fun i p ↦ (g (i, p)).1, ComputableIn.fst.comp hg, fun i p ↦ ?_⟩
  obtain ⟨⟨_, hcsmall⟩, b, hb, hxb⟩ := hgood (i, p)
  have hcsmall' : (g (i, p)).2 < (2 ^ p : ℚ)⁻¹ := hcsmall
  have h1 : dist (Q.ι (g (i, p)).1) (y i) < ((g (i, p)).2 : ℝ) :=
    Metric.mem_ball'.mp (hsound i b _ hb hxb)
  have h2 : (((g (i, p)).2 : ℚ) : ℝ) < dyadicRadius p := by
    rw [dyadicRadius, inv_pow]
    have h := (Rat.cast_lt (K := ℝ)).mpr hcsmall'
    push_cast at h
    exact h
  exact h1.trans h2

/-- Core of the evaluation lemmas: an enumerable family of ball pairs that is sound and complete
at one point with a computable name yields computable names of the images, uniformly in the
index of the family. -/
theorem exists_names_of_ballRel {ι : Type*} [Primcodable ι] (hP : ComputablePresentationIn P A)
    {R : ι × (ℕ × ℚ) × (ℕ × ℚ) → Prop} (hR : IsREIn A R) {y : ι → Y} {x : X}
    (hsound : ∀ i b c, R (i, b, c) → x ∈ basicBall P b → y i ∈ basicBall Q c)
    (hcomplete : ∀ i c, y i ∈ basicBall Q c → ∃ b, R (i, b, c) ∧ x ∈ basicBall P b)
    {a : ℕ → ℕ} (ha : IsCauchyName P x a) (hcomp : ComputableIn {charOracle A} a) :
    ∃ b : ι → ℕ → ℕ, ComputableIn {charOracle A} (fun ip : ι × ℕ ↦ b ip.1 ip.2) ∧
      ∀ i, IsCauchyName Q (y i) (b i) :=
  exists_names_of_ballRel_uniform hP hR (x := fun _ ↦ x) hsound hcomplete (a := fun _ ↦ a)
    (fun _ ↦ ha) (hcomp.comp ComputableIn.snd)

/-- Uniform evaluation of a represented family at points with uniformly computable names:
one computable name function of `(i, k, p)`. -/
theorem IsRepresentedFamilyIn.names_uniform {ι κ : Type*} [Primcodable ι] [Primcodable κ]
    (hP : ComputablePresentationIn P A) {f : ι → X → Y} (hf : IsRepresentedFamilyIn P Q A f)
    {x : κ → X} {a : κ → ℕ → ℕ} (ha : ∀ k, IsCauchyName P (x k) (a k))
    (hcomp : ComputableIn {charOracle A} fun kp : κ × ℕ ↦ a kp.1 kp.2) :
    ∃ b : ι → κ → ℕ → ℕ,
      ComputableIn {charOracle A} (fun w : (ι × κ) × ℕ ↦ b w.1.1 w.1.2 w.2) ∧
        ∀ i k, IsCauchyName Q (f i (x k)) (b i k) := by
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  obtain ⟨b, hb, hname⟩ := exists_names_of_ballRel_uniform (ι := ι × κ) hP
    (R := fun w ↦ R (w.1.1, w.2)) (hR.comp ((Computable.fst.comp Computable.fst).pair
      Computable.snd).computableIn) (y := fun w ↦ f w.1 (x w.2)) (x := fun w ↦ x w.2)
    (fun w b c h hxb ↦ (hsound w.1 b c h).2.2 (Set.mem_image_of_mem (f w.1) hxb))
    (fun w c hc ↦ hcomplete w.1 (x w.2) c hc) (a := fun w ↦ a w.2) (fun w ↦ ha w.2)
    (hcomp.comp ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd))
  exact ⟨fun i k ↦ b (i, k), hb, fun i k ↦ hname (i, k)⟩

/-- Preimages of a c.e. open family under a represented family of maps are c.e. open,
uniformly in both indices. -/
theorem IsRepresentedFamilyIn.preimage_ceOpen {ι κ : Type*} [Primcodable ι] [Primcodable κ]
    {f : ι → X → Y} (hf : IsRepresentedFamilyIn P Q A f) {U : κ → Set Y}
    (hU : IsCeOpenFamilyIn Q A U) :
    IsCeOpenFamilyIn P A fun d : ι × κ ↦ f d.1 ⁻¹' U d.2 := by
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  obtain ⟨E, hE, hU⟩ := hU
  refine ⟨fun db ↦ ∃ c, R (db.1.1, db.2, c) ∧ E (db.1.2, c), ?_, fun d ↦ ?_⟩
  · have h1 : ComputableIn {charOracle A} fun w : ((ι × κ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        (w.1.1.1, w.1.2, w.2) :=
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd)).computableIn
    have h2 : ComputableIn {charOracle A} fun w : ((ι × κ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        (w.1.1.2, w.2) :=
      ((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        Computable.snd).computableIn
    exact IsREIn.exists ((hR.comp h1).and (hE.comp h2))
  · ext x
    constructor
    · intro hx
      have hx' : f d.1 x ∈ U d.2 := hx
      rw [hU d.2] at hx'
      obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx'
      obtain ⟨b, hb, hxb⟩ := hcomplete d.1 x c hxc
      exact Set.mem_iUnion₂.mpr ⟨b, ⟨c, hb, hc⟩, hxb⟩
    · intro hx
      obtain ⟨b, ⟨c, hb, hc⟩, hxb⟩ := Set.mem_iUnion₂.mp hx
      change f d.1 x ∈ U d.2
      rw [hU d.2]
      exact Set.mem_iUnion₂.mpr ⟨c, hc, (hsound d.1 b c hb).2.2 (Set.mem_image_of_mem _ hxb)⟩

end aux

section notions

variable (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)

/-- Each member of a represented family is a represented map. -/
theorem IsRepresentedFamilyIn.apply {ι : Type*} [Primcodable ι] {f : ι → X → Y}
    (hf : IsRepresentedFamilyIn P Q A f) (i : ι) : IsRepresentedMapIn P Q A (f i) := by
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  exact ⟨fun bc ↦ R (i, bc), hR.comp ((Computable.const i).pair Computable.id).computableIn,
    fun b c h ↦ hsound i b c h, fun x c hx ↦ hcomplete i x c hx⟩

/-- A represented family sends computable points to computable points, uniformly in the
index: one computable name function of `(i, p)`. -/
theorem IsRepresentedFamilyIn.names {ι : Type*} [Primcodable ι] (hP : ComputablePresentationIn P A)
    {f : ι → X → Y} (hf : IsRepresentedFamilyIn P Q A f) {x : X} {a : ℕ → ℕ}
    (ha : IsCauchyName P x a) (hcomp : ComputableIn {charOracle A} a) :
    ∃ b : ι → ℕ → ℕ, ComputableIn {charOracle A} (fun ip : ι × ℕ ↦ b ip.1 ip.2) ∧
      ∀ i, IsCauchyName Q (f i x) (b i) := by
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  exact exists_names_of_ballRel hP hR
    (fun i b c h hxb ↦ (hsound i b c h).2.2 (Set.mem_image_of_mem (f i) hxb))
    (fun i c hc ↦ hcomplete i x c hc) ha hcomp

/-- A map represented everywhere is represented on every subset. -/
theorem IsRepresentedMapIn.onSubset {f : X → Y} (hf : IsRepresentedMapIn P Q A f) (S : Set X) :
    IsRepresentedOnIn P Q A S f := by
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  refine ⟨R, hR, fun b c h ↦ ⟨(hsound b c h).1, (hsound b c h).2.1, ?_⟩,
    fun x _ c hx ↦ hcomplete x c hx⟩
  exact (Set.image_mono Set.inter_subset_left).trans (hsound b c h).2.2

/-- A map represented on `S` sends computable points of `S` to computable points. -/
theorem IsRepresentedOnIn.map (hP : ComputablePresentationIn P A) {S : Set X} {f : X → Y}
    (hf : IsRepresentedOnIn P Q A S f) {x : X} (hxS : x ∈ S) (hx : IsComputablePointIn P A x) :
    IsComputablePointIn Q A (f x) := by
  obtain ⟨a, ha, hcomp⟩ := hx
  obtain ⟨R, hR, hsound, hcomplete⟩ := hf
  obtain ⟨b, hb, hname⟩ := exists_names_of_ballRel (ι := Unit) hP (R := fun w ↦ R w.2)
    (hR.comp Computable.snd.computableIn) (y := fun _ ↦ f x)
    (fun _ b c h hxb ↦ (hsound b c h).2.2 ⟨x, ⟨hxb, hxS⟩, rfl⟩)
    (fun _ c hc ↦ hcomplete x hxS c hc) ha hcomp
  exact ⟨b (), hname (), hb.comp ((Computable.const ()).pair Computable.id).computableIn⟩

/-- Monotonicity in the oracle. -/
theorem isRepresentedFamilyIn_mono {ι : Type*} [Primcodable ι] {B : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) {f : ι → X → Y} (hf : IsRepresentedFamilyIn P Q A f) :
    IsRepresentedFamilyIn P Q B f := by
  obtain ⟨R, hR, hs, hc⟩ := hf
  exact ⟨R, hR.mono_oracle hAB, hs, hc⟩

/-- Monotonicity in the oracle. -/
theorem isRepresentedOnIn_mono {B : Set ℕ} (hAB : charOracle A ≤ᵀ charOracle B) {S : Set X}
    {f : X → Y} (hf : IsRepresentedOnIn P Q A S f) : IsRepresentedOnIn P Q B S f := by
  obtain ⟨R, hR, hs, hc⟩ := hf
  exact ⟨R, hR.mono_oracle hAB, hs, hc⟩

end notions

end Kolmogorov.PointToSet
