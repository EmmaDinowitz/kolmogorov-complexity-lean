/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.Presentation
import KolmogorovMathlib.Oracle.Closure

/-!
# Computable points and strict distance certificates

A point of a presented space is relatively computable when it has a Cauchy name computable in
the oracle (`IsComputablePointIn`); ideal points are computable, represented maps preserve
computability, and the notion persists above the oracle. The second half proves once the
"dovetailed strict inequality" idiom used by every effective search: for points with uniformly
computable names, the distances to the ideal points form a relatively computable real family
(`isComputableRealFamilyIn_dist_names`), so membership in a basic ball and strict rational
lower bounds on distances are relatively enumerable, uniformly in the index
(`isREIn_mem_basicBall_of_names`, `isREIn_rat_lt_dist_names`, `isREIn_rat_lt_dist_of_names`).
Blueprint nodes `eff:points`, `eff:distance-certificates`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A point is relatively computable when it has a Cauchy name computable in the oracle.
Blueprint node `geo:effective-data`. -/
def IsComputablePointIn (P : Presentation X) (A : Set ℕ) (x : X) : Prop :=
  ∃ a : ℕ → ℕ, IsCauchyName P x a ∧ ComputableIn {charOracle A} a

section aux

variable {P : Presentation X} {Q : Presentation Y} {A B : Set ℕ}

/-- The constant sequence at an ideal point is a Cauchy name of that point. -/
theorem isCauchyName_const (P : Presentation X) (i : ℕ) : IsCauchyName P (P.ι i) fun _ ↦ i := by
  intro p
  rw [dist_self]
  exact dyadicRadius_pos p

/-- Every point of a presented space lies in a positive rational basic ball of radius below
any requested inverse power of two. -/
theorem exists_mem_basicBall_radius_lt (Q : Presentation Y) (y : Y) (p : ℕ) :
    ∃ c : ℕ × ℚ, y ∈ basicBall Q c ∧ 0 < c.2 ∧ c.2 < (2 ^ p : ℚ)⁻¹ := by
  have hpos : (0 : ℝ) < (2 ^ p : ℝ)⁻¹ := by positivity
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp Q.dense y ((2 ^ p : ℝ)⁻¹ / 2) (by positivity)
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn (show (2 ^ p : ℝ)⁻¹ / 2 < (2 ^ p : ℝ)⁻¹ by linarith)
  refine ⟨(j, r), Metric.mem_ball.mpr (hj.trans hr), ?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < (2 ^ p : ℝ)⁻¹ / 2 by positivity).trans hr
  · have h : ((r : ℚ) : ℝ) < (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := by
      push_cast
      exact hr'
    exact Rat.cast_lt.mp h

/-- Every point has a Cauchy name (density of the ideal points). -/
theorem exists_isCauchyName (P : Presentation X) (x : X) : ∃ a : ℕ → ℕ, IsCauchyName P x a := by
  have h : ∀ p : ℕ, ∃ n, dist (P.ι n) x < dyadicRadius p := fun p ↦ by
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.mp P.dense x (dyadicRadius p) (dyadicRadius_pos p)
    exact ⟨n, by rwa [dist_comm]⟩
  choose a ha using h
  exact ⟨a, ha⟩

/-- Distances from points with relatively computable names to the ideal points form a
relatively computable real family, uniformly in the index of the name. -/
theorem isComputableRealFamilyIn_dist_names {ι : Type*} [Primcodable ι]
    (hP : ComputablePresentationIn P A) {x : ι → X} {a : ι → ℕ → ℕ}
    (ha : ∀ i, IsCauchyName P (x i) (a i))
    (hcomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 ip.2) :
    IsComputableRealFamilyIn A fun ik : ι × ℕ ↦ dist (x ik.1) (P.ι ik.2) := by
  obtain ⟨q, hq, hqerr⟩ := hP
  refine ⟨fun ikp ↦ q ((a ikp.1.1 (ikp.2 + 1), ikp.1.2), ikp.2 + 1), ?_, ?_⟩
  · have hsucc : ComputableIn {charOracle A} fun ikp : (ι × ℕ) × ℕ ↦ ikp.2 + 1 :=
      (Computable.succ.comp Computable.snd).computableIn
    have h1 : ComputableIn {charOracle A} fun ikp : (ι × ℕ) × ℕ ↦ a ikp.1.1 (ikp.2 + 1) :=
      hcomp.comp ((ComputableIn.fst.comp ComputableIn.fst).pair hsucc)
    exact hq.comp ((h1.pair (ComputableIn.snd.comp ComputableIn.fst)).pair hsucc)
  · rintro ⟨i, k⟩ p
    change |(q ((a i (p + 1), k), p + 1) : ℝ) - dist (x i) (P.ι k)| < (2 : ℝ)⁻¹ ^ p
    have h1 := hqerr (a i (p + 1), k) (p + 1)
    have h2 := ha i (p + 1)
    simp only [dyadicRadius] at h2
    have h3 := abs_dist_sub_le (P.ι (a i (p + 1))) (x i) (P.ι k)
    calc |(q ((a i (p + 1), k), p + 1) : ℝ) - dist (x i) (P.ι k)|
        ≤ |(q ((a i (p + 1), k), p + 1) : ℝ) - dist (P.ι (a i (p + 1))) (P.ι k)| +
          |dist (P.ι (a i (p + 1))) (P.ι k) - dist (x i) (P.ι k)| := abs_sub_le _ _ _
      _ < (2 : ℝ)⁻¹ ^ (p + 1) + (2 : ℝ)⁻¹ ^ (p + 1) := add_lt_add_of_lt_of_le h1 (h3.trans_lt h2).le
      _ = (2 : ℝ)⁻¹ ^ p := by ring

/-- Distances from a point with a relatively computable name to the ideal points form a
relatively computable real family. -/
theorem isComputableRealFamilyIn_dist_name (hP : ComputablePresentationIn P A) {x : X}
    {a : ℕ → ℕ} (ha : IsCauchyName P x a) (hcomp : ComputableIn {charOracle A} a) :
    IsComputableRealFamilyIn A fun k : ℕ ↦ dist x (P.ι k) := by
  have h := isComputableRealFamilyIn_dist_names (ι := Unit) hP (x := fun _ ↦ x) (a := fun _ ↦ a)
    (fun _ ↦ ha) (hcomp.comp ComputableIn.snd)
  exact IsComputableRealFamilyIn.comp A _ h (fun k ↦ ((), k))
    ((Computable.const ()).pair Computable.id)

/-- Membership of a point with a relatively computable name in a basic ball is relatively
enumerable (a strict rational comparison of a computable real). -/
theorem isREIn_mem_basicBall_of_name (hP : ComputablePresentationIn P A) {x : X} {a : ℕ → ℕ}
    (ha : IsCauchyName P x a) (hcomp : ComputableIn {charOracle A} a) :
    IsREIn A fun b : ℕ × ℚ ↦ x ∈ basicBall P b := by
  have h := birkhoff_computableIn_lt A _ (isComputableRealFamilyIn_dist_name hP ha hcomp)
  have heq : (fun b : ℕ × ℚ ↦ x ∈ basicBall P b) =
      fun iq : ℕ × ℚ ↦ dist x (P.ι iq.1) < (iq.2 : ℝ) := by
    ext b
    exact Metric.mem_ball
  rw [heq]
  exact h

/-- Membership of points with uniformly computable names in basic balls is relatively
enumerable, uniformly in the index. -/
theorem isREIn_mem_basicBall_of_names {ι : Type*} [Primcodable ι]
    (hP : ComputablePresentationIn P A) {x : ι → X} {a : ι → ℕ → ℕ}
    (ha : ∀ i, IsCauchyName P (x i) (a i))
    (hcomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 ip.2) :
    IsREIn A fun ib : ι × (ℕ × ℚ) ↦ x ib.1 ∈ basicBall P ib.2 := by
  have h := (birkhoff_computableIn_lt A _ (isComputableRealFamilyIn_dist_names hP ha hcomp)).comp
    ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)).computableIn
  have heq : (fun ib : ι × (ℕ × ℚ) ↦ x ib.1 ∈ basicBall P ib.2) =
      fun ib : ι × (ℕ × ℚ) ↦ dist (x ib.1) (P.ι ib.2.1) < (ib.2.2 : ℝ) := by
    ext ib
    exact Metric.mem_ball
  rw [heq]
  exact h

/-- Strict rational lower bounds on the distances from points with uniformly computable names
to the ideal points are relatively enumerable. -/
theorem isREIn_rat_lt_dist_names {ι : Type*} [Primcodable ι]
    (hP : ComputablePresentationIn P A) {x : ι → X} {a : ι → ℕ → ℕ}
    (ha : ∀ i, IsCauchyName P (x i) (a i))
    (hcomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 ip.2) :
    IsREIn A fun w : (ι × ℕ) × ℚ ↦ (w.2 : ℝ) < dist (x w.1.1) (P.ι w.1.2) :=
  birkhoff_computableIn_gt A _ (isComputableRealFamilyIn_dist_names hP ha hcomp)

/-- The distances between two families of points with uniformly computable names form a
relatively computable real family (approximate both points at precision `p + 2`). -/
theorem isComputableRealFamilyIn_dist_of_names {ι : Type*} [Primcodable ι]
    (hP : ComputablePresentationIn P A) {x y : ι → X} {a b : ι → ℕ → ℕ}
    (ha : ∀ i, IsCauchyName P (x i) (a i))
    (hacomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 ip.2)
    (hb : ∀ i, IsCauchyName P (y i) (b i))
    (hbcomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ b ip.1 ip.2) :
    IsComputableRealFamilyIn A fun i : ι ↦ dist (x i) (y i) := by
  obtain ⟨q, hq, hqerr⟩ := hP
  refine ⟨fun ip ↦ q ((a ip.1 (ip.2 + 2), b ip.1 (ip.2 + 2)), ip.2 + 2), ?_, ?_⟩
  · have h2 : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ ip.2 + 2 :=
      ((Primrec.nat_add.comp Primrec.snd (Primrec.const 2)).to_comp).computableIn
    have h1 : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 (ip.2 + 2) :=
      hacomp.comp (ComputableIn.fst.pair h2)
    have h1' : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ b ip.1 (ip.2 + 2) :=
      hbcomp.comp (ComputableIn.fst.pair h2)
    exact hq.comp ((h1.pair h1').pair h2)
  · intro i p
    have h1 := hqerr (a i (p + 2), b i (p + 2)) (p + 2)
    have h2 := ha i (p + 2)
    have h3 := hb i (p + 2)
    simp only [dyadicRadius] at h2 h3
    have htri : |dist (P.ι (a i (p + 2))) (P.ι (b i (p + 2))) - dist (x i) (y i)| ≤
        dist (P.ι (a i (p + 2))) (x i) + dist (P.ι (b i (p + 2))) (y i) := by
      have t1 := abs_dist_sub_le (P.ι (a i (p + 2))) (x i) (P.ι (b i (p + 2)))
      have t2 := abs_dist_sub_le (P.ι (b i (p + 2))) (y i) (x i)
      rw [dist_comm (P.ι (b i (p + 2))) (x i), dist_comm (y i) (x i)] at t2
      calc |dist (P.ι (a i (p + 2))) (P.ι (b i (p + 2))) - dist (x i) (y i)|
          ≤ |dist (P.ι (a i (p + 2))) (P.ι (b i (p + 2))) - dist (x i) (P.ι (b i (p + 2)))| +
            |dist (x i) (P.ι (b i (p + 2))) - dist (x i) (y i)| := abs_sub_le _ _ _
        _ ≤ dist (P.ι (a i (p + 2))) (x i) + dist (P.ι (b i (p + 2))) (y i) :=
            add_le_add t1 t2
    have h4 : (2 : ℝ)⁻¹ ^ (p + 2) + ((2 : ℝ)⁻¹ ^ (p + 2) + (2 : ℝ)⁻¹ ^ (p + 2)) <
        (2 : ℝ)⁻¹ ^ p := by
      have : (2 : ℝ)⁻¹ ^ (p + 2) = (2 : ℝ)⁻¹ ^ p / 4 := by ring
      rw [this]
      have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ p := by positivity
      linarith
    calc |(q ((a i (p + 2), b i (p + 2)), p + 2) : ℝ) - dist (x i) (y i)|
        ≤ |(q ((a i (p + 2), b i (p + 2)), p + 2) : ℝ) -
            dist (P.ι (a i (p + 2))) (P.ι (b i (p + 2)))| +
          |dist (P.ι (a i (p + 2))) (P.ι (b i (p + 2))) - dist (x i) (y i)| := abs_sub_le _ _ _
      _ < (2 : ℝ)⁻¹ ^ (p + 2) + ((2 : ℝ)⁻¹ ^ (p + 2) + (2 : ℝ)⁻¹ ^ (p + 2)) :=
          add_lt_add_of_lt_of_le h1 (htri.trans (add_le_add h2.le h3.le))
      _ < (2 : ℝ)⁻¹ ^ p := h4

/-- Strict rational lower bounds on the distance between two points with uniformly computable
names are relatively enumerable, uniformly in the index: `ρ < dist (x i) (y i)` holds exactly
when some stage `p` of the name of `y i` certifies `ρ + 2 · 2⁻ᵖ < dist (x i) (ι (b i p))`. -/
theorem isREIn_rat_lt_dist_of_names {ι : Type*} [Primcodable ι]
    (hP : ComputablePresentationIn P A) {x y : ι → X} {a b : ι → ℕ → ℕ}
    (ha : ∀ i, IsCauchyName P (x i) (a i))
    (hacomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ a ip.1 ip.2)
    (hb : ∀ i, IsCauchyName P (y i) (b i))
    (hbcomp : ComputableIn {charOracle A} fun ip : ι × ℕ ↦ b ip.1 ip.2) :
    IsREIn A fun w : ι × ℚ ↦ (w.2 : ℝ) < dist (x w.1) (y w.1) := by
  have hlt := isREIn_rat_lt_dist_names hP ha hacomp
  have hre : ComputableIn {charOracle A} fun v : (ι × ℚ) × ℕ ↦
      ((v.1.1, b v.1.1 v.2), v.1.2 + 2 * (2 ^ v.2 : ℚ)⁻¹) :=
    ((ComputableIn.fst.comp ComputableIn.fst).pair
      (hbcomp.comp ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))).pair
      (computable₂_ratAdd.computableIn₂.comp (ComputableIn.snd.comp ComputableIn.fst)
        (computable₂_ratMul.computableIn₂.comp (ComputableIn.const 2)
          (computable_rat_inv_two_pow.computableIn.comp ComputableIn.snd)))
  have h := (hlt.comp hre).exists
  have heq : (fun w : ι × ℚ ↦ (w.2 : ℝ) < dist (x w.1) (y w.1)) = fun w : ι × ℚ ↦
      ∃ p : ℕ, ((w.2 + 2 * (2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) < dist (x w.1) (P.ι (b w.1 p)) := by
    funext w
    apply propext
    constructor
    · intro hw
      obtain ⟨p, hp⟩ := exists_dyadicRadius_lt (show 0 < (dist (x w.1) (y w.1) - w.2) / 3 by
        linarith)
      have hp' : dyadicRadius p = ((2 ^ p : ℚ)⁻¹ : ℝ) := by
        rw [dyadicRadius, inv_pow]
        push_cast
        rfl
      have hname := hb w.1 p
      have htri := dist_triangle (x w.1) (P.ι (b w.1 p)) (y w.1)
      refine ⟨p, ?_⟩
      rw [hp'] at hp hname
      push_cast at hp hname ⊢
      linarith
    · rintro ⟨p, hp⟩
      have hp' : dyadicRadius p = ((2 ^ p : ℚ)⁻¹ : ℝ) := by
        rw [dyadicRadius, inv_pow]
        push_cast
        rfl
      have hname := hb w.1 p
      have htri := dist_triangle (x w.1) (y w.1) (P.ι (b w.1 p))
      rw [dist_comm] at hname
      rw [hp'] at hname
      push_cast at hp hname
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ p)⁻¹ := by positivity
      linarith
  rw [heq]
  exact h

end aux

section notions

variable (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)

/-- Every ideal point is computable. -/
theorem isComputablePointIn_ι (_hP : ComputablePresentationIn P A) (i : ℕ) :
    IsComputablePointIn P A (P.ι i) :=
  ⟨fun _ ↦ i, isCauchyName_const P i, ComputableIn.const i⟩

/-- A represented map sends computable points to computable points
(wrapper around `eval_computable_names`). -/
theorem IsComputablePointIn.map (hP : ComputablePresentationIn P A) {f : X → Y}
    (hf : IsRepresentedMapIn P Q A f) {x : X} (hx : IsComputablePointIn P A x) :
    IsComputablePointIn Q A (f x) := by
  obtain ⟨a, ha, hcomp⟩ := hx
  obtain ⟨b, hb, hbc⟩ := eval_computable_names P Q A hP f hf x a ha hcomp
  exact ⟨b, hb, hbc⟩

/-- Membership of a computable point in a basic ball is semidecidable (strict rational
inequality on a computable real). -/
theorem isREIn_mem_basicBall (hP : ComputablePresentationIn P A) {x : X} {a : ℕ → ℕ}
    (ha : IsCauchyName P x a) (hcomp : ComputableIn {charOracle A} a) :
    IsREIn A fun b : ℕ × ℚ ↦ x ∈ basicBall P b :=
  isREIn_mem_basicBall_of_name hP ha hcomp

/-- Monotonicity in the oracle: every notion persists above `A`. -/
theorem isComputablePointIn_mono {B : Set ℕ} (hAB : charOracle A ≤ᵀ charOracle B) {x : X}
    (hx : IsComputablePointIn P A x) : IsComputablePointIn P B x := by
  obtain ⟨a, ha, hcomp⟩ := hx
  exact ⟨a, ha, computableIn_mono_oracle hcomp hAB⟩

end notions

end Kolmogorov.PointToSet
