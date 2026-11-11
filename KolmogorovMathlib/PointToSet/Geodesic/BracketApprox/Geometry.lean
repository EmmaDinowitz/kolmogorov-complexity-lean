/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.Localization

/-!
# Local products from finite orbit data: the geometry (geodesic blueprint, Chapter E, part 1)

The geometric steps of the node `geo:bracket-approx` (OTL `lem:local_product_approximator`):
the bracket constructions `y = φ (-T) [φ T [p,x]_s, q]_s` and their backward counterparts lie
in the shadow sets of Chapter D (`bracket_construction_mem_shadowSet`, `_Backward`) and are
within `C₁ E_±(ρ)` of the brackets `[p,x]_s`, `[x,p]_u` (`bracket_construction_error`,
`_backward`); the decoded point is unique near a compact regular set
(`shadowSet_subsingleton_of_mem`, `shadowSetBackward_subsingleton_of_mem`). The compact
plaques of marked points must lie inside the expansivity plaques of the decoder; this
is the explicit hypothesis `SmallPlaques`, discharged by `smallPlaques` from the shrinkable
plaques of Chapter B. The programs themselves are in `BracketApprox.lean`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
/-- Bowen balls grow with the radius. -/
theorem bowenBall_mono_radius (T : X → X) (n : ℕ) (x : X) {ε ε' : ℝ} (hle : ε ≤ ε') :
    bowenBall T n x ε ⊆ bowenBall T n x ε' := fun _ hy ↦
  Dynamics.dynEntourage_monotone T n (fun _ hz ↦ lt_of_lt_of_le hz hle) hy

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-- A compact regular neighborhood of a compact regular set: a small closed thickening. -/
theorem exists_compact_nhds_regular {Pp : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg) :
    ∃ Q : Set X, IsCompact Q ∧ Pp ⊆ interior Q ∧ Q ⊆ G.Reg := by
  obtain ⟨t, ht, htQ⟩ := hPp.exists_thickening_subset_open G.isOpen_Reg hPpR
  refine ⟨Metric.cthickening (t / 2) Pp, hPp.cthickening, ?_, ?_⟩
  · exact (Metric.self_subset_thickening (by positivity) Pp).trans
      (interior_maximal (Metric.thickening_subset_cthickening _ _) Metric.isOpen_thickening)
  · exact (Metric.cthickening_subset_thickening' ht (by linarith) Pp).trans htQ

/-- The compact plaques of the points of `Q` lie in the `ε₀`-plaques (needed by
the decoder; see the module docstring). Blueprint node `geo:bracket-approx`. -/
def SmallPlaques (Q : Set X) (ε₀ : ℝ) : Prop :=
  ∀ p ∈ Q, ∀ r : ℚ, 0 < r → (r : ℝ) ≤ ε₀ →
    G.Kplaque r p ⊆ closure (G.plaque .u ε₀ p) ∧ G.Kplaque' r p ⊆ closure (G.plaque .s ε₀ p)

/-- With shrinkable plaques (`Kplaque_spec`, blueprint item 8.1) the small-plaque condition
holds for every compact set and every threshold. -/
theorem smallPlaques (Q : Set X) (ε₀ : ℝ) : G.SmallPlaques Q ε₀ := fun _ _ _ hr hrε ↦
  ⟨G.Kplaque_subset_closure_plaque hr hrε, G.Kplaque'_subset_closure_plaque hr hrε⟩

end GeodesicReconstructionData

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-! ### `geo:bracket-approx`: geometric steps -/

/-- The forward bracket construction. For `a = [p,x]_s`, `b = φ T a`, a marked `q` close to
`φ T x`, `c = [b,q]_s` and `y = φ (-T) c`: `y` lies on the unstable leaf of `p`, in its compact
plaque, and shadows the orbit of `x` on `[0, T]` and the orbit of `q` after `T` within the
decoder tolerance. This is the shadowing description of `y` (marked past of `p`, middle
orbit of `x`, marked future of `q`). Blueprint node `geo:bracket-approx`. -/
theorem bracket_construction_mem_shadowSet {Pp : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    (ρ' : ℝ) (hρ' : 0 < ρ') (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧ ∃ r : ℚ, 0 < r ∧ (r : ℝ) ≤ ε₀ ∧
      ∀ x ∈ G.Reg, ∃ δ : ℝ, 0 < δ ∧
        ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (T : ℝ) x ∈ Pp →
          ∀ i, P.ι i ∈ bowenBall G.f (T + 1) x ε →
            ∀ kq, dist (E.pIdx kq) (G.φ (T : ℝ) x) < η →
              G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)) ∈
                E.shadowSet ρ' r kp i T kq := by
  obtain ⟨δP, hδP, κP, hκP, hlpsP⟩ := G.lps Pp hPp hPpR
  have hκP0 : 0 < κP := by linarith
  have hrLeaf := G.rLeaf_pos
  have hCc := G.Cc_nonneg
  have hCLeaf : 0 < G.CLeaf := by linarith [G.one_le_CLeaf]
  have hL : 0 < G.L := by linarith [G.one_le_L]
  -- the plaque radius
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show (0 : ℝ) < min ε₀ G.rLeaf by positivity)
  have hrε : (r : ℝ) ≤ ε₀ := hr1.le.trans (min_le_left _ _)
  have hrL : (r : ℝ) ≤ G.rLeaf := hr1.le.trans (min_le_right _ _)
  -- the tolerance `δ'` near `Pp`: `κP δ'` below `δP`, `rLeaf`, `r/4` and `ρ'/(3 M)`
  set M : ℝ := G.CLeaf + G.Cc + 1 with hMdef
  have hM : 0 < M := by positivity
  set δ' : ℝ := min δP (min (G.rLeaf / κP) (min (r / 4 / κP) (ρ' / (3 * M) / κP))) with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'P : δ' ≤ δP := min_le_left _ _
  have hδ'r : κP * δ' ≤ G.rLeaf := by
    have : δ' ≤ G.rLeaf / κP := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'q : κP * δ' ≤ r / 4 := by
    have : δ' ≤ r / 4 / κP :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'ρ : κP * δ' ≤ ρ' / (3 * M) := by
    have : δ' ≤ ρ' / (3 * M) / κP :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'C : G.CLeaf * (κP * δ') ≤ ρ' / 3 := by
    have h1 : G.CLeaf * (κP * δ') ≤ G.CLeaf * (ρ' / (3 * M)) :=
      mul_le_mul_of_nonneg_left hδ'ρ hCLeaf.le
    have h2 : G.CLeaf * (ρ' / (3 * M)) ≤ ρ' / 3 := by
      calc G.CLeaf * (ρ' / (3 * M)) ≤ M * (ρ' / (3 * M)) :=
            mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) (by positivity)
        _ = ρ' / 3 := by field_simp
    exact h1.trans h2
  have hδ'Cc : G.Cc * (κP * δ') ≤ ρ' / 3 := by
    have h1 : G.Cc * (κP * δ') ≤ G.Cc * (ρ' / (3 * M)) := mul_le_mul_of_nonneg_left hδ'ρ hCc
    have h2 : G.Cc * (ρ' / (3 * M)) ≤ ρ' / 3 := by
      calc G.Cc * (ρ' / (3 * M)) ≤ M * (ρ' / (3 * M)) :=
            mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) (by positivity)
        _ = ρ' / 3 := by field_simp
    exact h1.trans h2
  refine ⟨ρ' / (3 * G.L), by positivity, δ' / 2, by positivity, r, by exact_mod_cast hr0, hrε,
    fun x hx ↦ ?_⟩
  obtain ⟨δx, hδx, κx, hκx, hlpsx⟩ :=
    G.lps {x} isCompact_singleton (Set.singleton_subset_iff.2 hx)
  have hκx0 : 0 < κx := by linarith
  -- the admissible radius about `x`: `κx δ` below `rLeaf`, `r/4`, `ρ'/(3 Cc + 3)`, and
  -- `Cc κx δ < δ'/2`
  set δ : ℝ := min δx (min (G.rLeaf / κx) (min (r / 4 / κx)
    (min (ρ' / (3 * (G.Cc + 1)) / κx) (δ' / 2 / (G.Cc * κx + 1))))) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδx' : δ ≤ δx := min_le_left _ _
  have hδr : κx * δ ≤ G.rLeaf := by
    have : δ ≤ G.rLeaf / κx := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hκx0, mul_comm] at this
  have hδq : κx * δ ≤ r / 4 := by
    have : δ ≤ r / 4 / κx :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ hκx0, mul_comm] at this
  have hδρ : G.Cc * (κx * δ) ≤ ρ' / 3 := by
    have : δ ≤ ρ' / (3 * (G.Cc + 1)) / κx :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ hκx0, mul_comm] at this
    have h1 : G.Cc * (κx * δ) ≤ G.Cc * (ρ' / (3 * (G.Cc + 1))) :=
      mul_le_mul_of_nonneg_left this hCc
    have h2 : G.Cc * (ρ' / (3 * (G.Cc + 1))) ≤ ρ' / 3 := by
      calc G.Cc * (ρ' / (3 * (G.Cc + 1))) ≤ (G.Cc + 1) * (ρ' / (3 * (G.Cc + 1))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ρ' / 3 := by field_simp
    exact h1.trans h2
  have hδ'' : G.Cc * (κx * δ) < δ' / 2 := by
    have h2 : δ ≤ δ' / 2 / (G.Cc * κx + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have h3 : G.Cc * (κx * δ) ≤ G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) < δ' / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hCc hκx0.le]
    exact h3.trans_lt h4
  refine ⟨δ, hδpos, fun kp hkp T hT i hi kq hkq ↦ ?_⟩
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  -- notation: `p`, `a = [p, x]_s`, `b = φ T a`, `q`, `c = [b, q]_s`, `y = φ (-T) c`
  set p := E.pIdx kp with hpdef
  set a := G.bracketS p x with hadef
  set b := G.φ (T : ℝ) a with hbdef
  set q := E.pIdx kq with hqdef
  set c := G.bracketS b q with hcdef
  -- the local product at `x`
  have hdpx : dist p x < δx := lt_of_lt_of_le hkp hδx'
  have hinfx : ∃ q ∈ ({x} : Set _), dist p q < δx := ⟨x, Set.mem_singleton x, hdpx⟩
  obtain ⟨⟨haWu, hlegu, haW, hleg, -⟩, -⟩ := hlpsx p x hinfx hdpx
  have hu : G.dW .u p a < κx * δ := lt_of_le_of_lt hlegu (mul_lt_mul_of_pos_left hkp hκx0)
  have hcs : G.dW .cs x a < κx * δ := lt_of_le_of_lt hleg (mul_lt_mul_of_pos_left hkp hκx0)
  have hcs_r : G.dW .cs x a < G.rLeaf := hcs.trans_le hδr
  -- `b` is close to `φ T x`, hence to `Pp` and to `q`
  have hbx : ∀ t : ℝ, 0 ≤ t → dist (G.φ t a) (G.φ t x) ≤ G.Cc * (κx * δ) := fun t ht ↦
    (G.center_leg_cs x a haW hcs_r t ht).trans (mul_le_mul_of_nonneg_left hcs.le hCc)
  have hbx' : dist b (G.φ (T : ℝ) x) < δ' / 2 := (hbx T hT0).trans_lt hδ''
  have hinfb : ∃ q ∈ Pp, dist b q < δP := ⟨_, hT, hbx'.trans_le (by linarith)⟩
  have hdbq : dist b q < δ' := by
    calc dist b q ≤ dist b (G.φ (T : ℝ) x) + dist (G.φ (T : ℝ) x) q := dist_triangle _ _ _
      _ < δ' / 2 + δ' / 2 := add_lt_add hbx' (by rwa [dist_comm])
      _ = δ' := by ring
  -- the local product at `Pp`
  obtain ⟨⟨hcW, hlegc, hcWcs, hlegcs, -⟩, -⟩ := hlpsP b q hinfb (hdbq.trans_le hδ'P)
  have hc : G.dW .u b c < κP * δ' := lt_of_le_of_lt hlegc (mul_lt_mul_of_pos_left hdbq hκP0)
  have hccs : G.dW .cs q c < κP * δ' :=
    lt_of_le_of_lt hlegcs (mul_lt_mul_of_pos_left hdbq hκP0)
  -- `y` on the unstable leaf of `a`, hence of `p`
  have hba : G.φ (-(T : ℝ)) b = a := by
    rw [hbdef, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have hyWa : G.φ (-(T : ℝ)) c ∈ G.W .u a := by
    have := G.mem_W_flow hcW (-(T : ℝ))
    rwa [hba] at this
  have hWap : G.W .u a = G.W .u p := G.W_eq_of_mem _ _ _ haWu
  have hyWp : G.φ (-(T : ℝ)) c ∈ G.W .u p := by rwa [hWap] at hyWa
  have hdWay : G.dW .u a (G.φ (-(T : ℝ)) c) ≤ G.dW .u b c := by
    have := G.dW_u_flow_le b c hcW T hT0
    rwa [hba] at this
  refine ⟨?_, fun j hj ↦ ?_, fun n ↦ ?_⟩
  · -- the plaque constraint
    refine (G.Kplaque_spec p r (by exact_mod_cast hr0)).2.1 ⟨hyWp, ?_⟩
    calc G.dW .u p (G.φ (-(T : ℝ)) c)
        ≤ G.dW .u p a + G.dW .u a (G.φ (-(T : ℝ)) c) := G.dW_triangle _ _ _ _ haWu hyWp
      _ < κx * δ + κP * δ' := add_lt_add_of_lt_of_le hu (hdWay.trans hc.le)
      _ ≤ r / 4 + r / 4 := add_le_add hδq hδ'q
      _ = (r : ℝ) / 2 := by ring
  · -- the middle constraint at an integer time `j ≤ T`
    have hj' : (j : ℝ) ≤ T := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hs0 : (0 : ℝ) ≤ (T : ℝ) - j := by linarith
    -- `φ j y = φ (-(T - j)) c` and `φ j a = φ (-(T - j)) b`
    have e₁ : G.φ (j : ℝ) (G.φ (-(T : ℝ)) c) = G.φ (-((T : ℝ) - j)) c := by
      rw [← Flow.map_add]
      congr 1
      ring
    have e₂ : G.φ (j : ℝ) a = G.φ (-((T : ℝ) - j)) b := by
      rw [hbdef, ← Flow.map_add]
      congr 1
      ring
    have hleaf : G.dW .u (G.φ (j : ℝ) a) (G.φ (j : ℝ) (G.φ (-(T : ℝ)) c)) ≤ G.dW .u b c := by
      rw [e₁, e₂]
      exact G.dW_u_flow_le b c hcW _ hs0
    have hmemj : G.φ (j : ℝ) (G.φ (-(T : ℝ)) c) ∈ G.W .u (G.φ (j : ℝ) a) := by
      rw [e₁, e₂]
      exact G.mem_W_flow hcW _
    have hA : dist (G.φ (j : ℝ) a) (G.φ (j : ℝ) (G.φ (-(T : ℝ)) c)) ≤ G.CLeaf * (κP * δ') := by
      have h1 := G.dist_le_CLeaf_mul_dW .u _ _ hmemj (hleaf.trans_lt (hc.trans_le hδ'r))
      exact h1.trans (mul_le_mul_of_nonneg_left (hleaf.trans hc.le) hCLeaf.le)
    have hB := hbx j hj0
    have hC : dist (G.φ (j : ℝ) x) (G.φ (j : ℝ) (P.ι i)) < G.L * (ρ' / (3 * G.L)) :=
      G.toFlowData.dist_flow_lt_of_mem_bowenBall hi hj0 hj'
    have hC' : G.L * (ρ' / (3 * G.L)) = ρ' / 3 := by
      field_simp
    rw [hC'] at hC
    calc dist (G.φ (j : ℝ) (G.φ (-(T : ℝ)) c)) (G.φ (j : ℝ) (P.ι i))
        ≤ dist (G.φ (j : ℝ) (G.φ (-(T : ℝ)) c)) (G.φ (j : ℝ) a) +
            dist (G.φ (j : ℝ) a) (G.φ (j : ℝ) x) +
            dist (G.φ (j : ℝ) x) (G.φ (j : ℝ) (P.ι i)) := dist_triangle4 _ _ _ _
      _ ≤ ρ' / 3 + ρ' / 3 + ρ' / 3 := by
          rw [dist_comm (G.φ (j : ℝ) (G.φ (-(T : ℝ)) c))]
          exact add_le_add (add_le_add (hA.trans hδ'C) (hB.trans hδρ)) hC.le
      _ = ρ' := by ring
  · -- the future constraint: `φ (T + n) y = φ n c` shadows `φ n q` along the center stable leg
    have e₃ : G.φ ((T : ℝ) + n) (G.φ (-(T : ℝ)) c) = G.φ (n : ℝ) c := by
      rw [← Flow.map_add]
      congr 1
      ring
    rw [e₃]
    have h1 := G.center_leg_cs q c hcWcs (hccs.trans_le hδ'r) n (Nat.cast_nonneg n)
    rw [dist_comm]
    calc dist (G.φ (n : ℝ) q) (G.φ (n : ℝ) c) ≤ G.Cc * G.dW .cs q c := by
          rw [dist_comm]
          exact h1
      _ ≤ G.Cc * (κP * δ') := mul_le_mul_of_nonneg_left hccs.le hCc
      _ ≤ ρ' / 3 := hδ'Cc
      _ ≤ ρ' := by linarith

/-- The error of the forward bracket construction: with `a = [p,x]_s` and `y` as above,
`d^u(y, a)` is at most a constant times `E₊(ρ)`, by leafwise contraction (G5) along the orbit
of `a`, the rate comparison along the center stable leg from `a` to `x`, and the time reversal
`s = T - τ`. Blueprint node `geo:bracket-approx`. -/
theorem bracket_construction_error {Pp : Set X} (hPp : IsCompact Pp) (hPpR : Pp ⊆ G.Reg)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ η : ℝ, 0 < η ∧ ∀ x ∈ G.Reg, ∃ δ : ℝ, 0 < δ ∧
      ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (T : ℝ) x ∈ Pp →
        ∀ kq, dist (E.pIdx kq) (G.φ (T : ℝ) x) < η →
          dist (G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)))
              (G.bracketS (E.pIdx kp) x) ≤
            C' * G.scalePlus ρ T x := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  set β : ℝ := ρ * Real.log 2 / 2 with hβdef
  have hβ : 0 < β := by positivity
  obtain ⟨δβ, hδβ, hcontr⟩ := G.dW_u_flow_neg_le_of_accumulatedRate β hβ
  obtain ⟨δacc, hδacc, hacc⟩ := G.accumulatedRate_close_of_cs_leg β hβ
  obtain ⟨δP, hδP, κP, hκP, hlpsP⟩ := G.lps Pp hPp hPpR
  have hκP0 : 0 < κP := by linarith
  have hrLeaf := G.rLeaf_pos
  have hCc := G.Cc_nonneg
  have hCLeaf : 0 < G.CLeaf := by linarith [G.one_le_CLeaf]
  set δ' : ℝ := min δP (min (δβ / κP) (G.rLeaf / κP)) with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'P : δ' ≤ δP := min_le_left _ _
  have hδ'β : κP * δ' ≤ δβ := by
    have : δ' ≤ δβ / κP := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'r : κP * δ' ≤ G.rLeaf := by
    have : δ' ≤ G.rLeaf / κP := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  refine ⟨G.CLeaf * κP * δ', by positivity, δ' / 2, by positivity, fun x hx ↦ ?_⟩
  obtain ⟨δx, hδx, κx, hκx, hlpsx⟩ :=
    G.lps {x} isCompact_singleton (Set.singleton_subset_iff.2 hx)
  have hκx0 : 0 < κx := by linarith
  set δ : ℝ := min δx (min (δacc / κx) (min (G.rLeaf / κx) (δ' / 2 / (G.Cc * κx + 1))))
    with hδdef
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun kp hkp T hT kq hkq ↦ ?_⟩
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hdpx : dist (E.pIdx kp) x < δx := lt_of_lt_of_le hkp (min_le_left _ _)
  have hinfx : ∃ q ∈ ({x} : Set _), dist (E.pIdx kp) q < δx := ⟨x, Set.mem_singleton x, hdpx⟩
  obtain ⟨⟨-, -, haW, hleg, -⟩, -⟩ := hlpsx (E.pIdx kp) x hinfx hdpx
  have hcs : G.dW .cs x (G.bracketS (E.pIdx kp) x) < κx * δ :=
    lt_of_le_of_lt hleg (mul_lt_mul_of_pos_left hkp hκx0)
  have hcs_acc : G.dW .cs x (G.bracketS (E.pIdx kp) x) < δacc := by
    have : δ ≤ δacc / κx := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ hκx0, mul_comm] at this
    exact hcs.trans_le this
  have hcs_r : G.dW .cs x (G.bracketS (E.pIdx kp) x) < G.rLeaf := by
    have : δ ≤ G.rLeaf / κx := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ hκx0, mul_comm] at this
    exact hcs.trans_le this
  have hbx : dist (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (G.φ (T : ℝ) x) < δ' / 2 := by
    have h1 := G.center_leg_cs x _ haW hcs_r T hT0
    have h2 : δ ≤ δ' / 2 / (G.Cc * κx + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have h3 : G.Cc * (κx * δ) ≤ G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) < δ' / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hCc hκx0.le]
    calc dist (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (G.φ (T : ℝ) x)
        ≤ G.Cc * G.dW .cs x (G.bracketS (E.pIdx kp) x) := h1
      _ ≤ G.Cc * (κx * δ) := mul_le_mul_of_nonneg_left hcs.le hCc
      _ < δ' / 2 := h3.trans_lt h4
  have hinfb : ∃ q ∈ Pp, dist (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) q < δP :=
    ⟨_, hT, hbx.trans_le (by linarith)⟩
  have hdbq : dist (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq) < δ' := by
    calc dist (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)
        ≤ dist (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (G.φ (T : ℝ) x) +
            dist (G.φ (T : ℝ) x) (E.pIdx kq) := dist_triangle _ _ _
      _ < δ' / 2 + δ' / 2 := add_lt_add hbx (by rwa [dist_comm])
      _ = δ' := by ring
  obtain ⟨⟨hcW, hlegc, -, -, -⟩, -⟩ :=
    hlpsP (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq) hinfb (hdbq.trans_le hδ'P)
  have hc : G.dW .u (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x))
      (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)) < κP * δ' :=
    lt_of_le_of_lt hlegc (mul_lt_mul_of_pos_left hdbq hκP0)
  have hba : G.φ (-(T : ℝ)) (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) =
      G.bracketS (E.pIdx kp) x := by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  have h1 := hcontr (G.bracketS (E.pIdx kp) x) _ T hT0 hcW (hc.trans_le hδ'β)
  have h2 := G.dW_u_flow_le _ _ hcW T hT0
  rw [hba] at h2
  have hmem := G.mem_W_flow hcW (-(T : ℝ))
  rw [hba] at hmem
  have hdist := G.dist_le_CLeaf_mul_dW .u _ _ hmem (h2.trans_lt (hc.trans_le hδ'r))
  have h3 := hacc x _ haW hcs_acc T hT0
  have h4 : Real.exp (-(G.toFlowData.accumulatedRate G.lamU T (G.bracketS (E.pIdx kp) x) - β * T)) ≤
      G.scalePlus ρ T x := by
    rw [G.scalePlus_eq_exp]
    apply Real.exp_le_exp.2
    have := (abs_le.1 h3).1
    have hβT : ρ * Real.log 2 * T = 2 * (β * T) := by rw [hβdef]; ring
    linarith
  rw [dist_comm]
  calc dist (G.bracketS (E.pIdx kp) x)
        (G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)))
      ≤ G.CLeaf * G.dW .u (G.bracketS (E.pIdx kp) x)
          (G.φ (-(T : ℝ)) (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq))) :=
        hdist
    _ ≤ G.CLeaf * (G.dW .u (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x))
          (G.bracketS (G.φ (T : ℝ) (G.bracketS (E.pIdx kp) x)) (E.pIdx kq)) *
          Real.exp (-(G.toFlowData.accumulatedRate G.lamU T (G.bracketS (E.pIdx kp) x) - β * T))) :=
        mul_le_mul_of_nonneg_left h1 hCLeaf.le
    _ ≤ G.CLeaf * ((κP * δ') * G.scalePlus ρ T x) := by
        apply mul_le_mul_of_nonneg_left _ hCLeaf.le
        exact mul_le_mul hc.le h4 (Real.exp_pos _).le (by positivity)
    _ = G.CLeaf * κP * δ' * G.scalePlus ρ T x := by ring

/-- The backward bracket construction: for `a = [x,p]_u`, `b = φ (-T) a`, a marked `q` close
to `φ (-T) x`, `c = [q,b]_u` and `y = φ T c`, the point `y` lies in the compact stable plaque
of `p` and its backward orbit shadows the backward orbit of `x` on `[0, T]` and the backward
orbit of `q` after `T`. Blueprint node `geo:bracket-approx` (reversed). -/
theorem bracket_construction_mem_shadowSetBackward {Pm : Set X} (hPm : IsCompact Pm)
    (hPmR : Pm ⊆ G.Reg) (ρ' : ℝ) (hρ' : 0 < ρ') (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧ ∃ r : ℚ, 0 < r ∧ (r : ℝ) ≤ ε₀ ∧
      ∀ x ∈ G.Reg, ∃ δ : ℝ, 0 < δ ∧
        ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (-(T : ℝ)) x ∈ Pm →
          ∀ i, P.ι i ∈ bowenBall G.finv (T + 1) x ε →
            ∀ kq, dist (E.pIdx kq) (G.φ (-(T : ℝ)) x) < η →
              G.φ (T : ℝ) (G.bracketU (E.pIdx kq) (G.φ (-(T : ℝ)) (G.bracketU x (E.pIdx kp)))) ∈
                E.shadowSetBackward ρ' r kp i T kq := by
  obtain ⟨δP, hδP, κP, hκP, hlpsP⟩ := G.lps Pm hPm hPmR
  have hκP0 : 0 < κP := by linarith
  have hrLeaf := G.rLeaf_pos
  have hCc := G.Cc_nonneg
  have hCLeaf : 0 < G.CLeaf := by linarith [G.one_le_CLeaf]
  have hL : 0 < G.L := by linarith [G.one_le_L]
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (show (0 : ℝ) < min ε₀ G.rLeaf by positivity)
  have hrε : (r : ℝ) ≤ ε₀ := hr1.le.trans (min_le_left _ _)
  set M : ℝ := G.CLeaf + G.Cc + 1 with hMdef
  have hM : 0 < M := by positivity
  set δ' : ℝ := min δP (min (G.rLeaf / κP) (min (r / 4 / κP) (ρ' / (3 * M) / κP))) with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'P : δ' ≤ δP := min_le_left _ _
  have hδ'r : κP * δ' ≤ G.rLeaf := by
    have : δ' ≤ G.rLeaf / κP := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'q : κP * δ' ≤ r / 4 := by
    have : δ' ≤ r / 4 / κP :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'ρ : κP * δ' ≤ ρ' / (3 * M) := by
    have : δ' ≤ ρ' / (3 * M) / κP :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'C : G.CLeaf * (κP * δ') ≤ ρ' / 3 := by
    have h1 : G.CLeaf * (κP * δ') ≤ G.CLeaf * (ρ' / (3 * M)) :=
      mul_le_mul_of_nonneg_left hδ'ρ hCLeaf.le
    have h2 : G.CLeaf * (ρ' / (3 * M)) ≤ ρ' / 3 := by
      calc G.CLeaf * (ρ' / (3 * M)) ≤ M * (ρ' / (3 * M)) :=
            mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) (by positivity)
        _ = ρ' / 3 := by field_simp
    exact h1.trans h2
  have hδ'Cc : G.Cc * (κP * δ') ≤ ρ' / 3 := by
    have h1 : G.Cc * (κP * δ') ≤ G.Cc * (ρ' / (3 * M)) := mul_le_mul_of_nonneg_left hδ'ρ hCc
    have h2 : G.Cc * (ρ' / (3 * M)) ≤ ρ' / 3 := by
      calc G.Cc * (ρ' / (3 * M)) ≤ M * (ρ' / (3 * M)) :=
            mul_le_mul_of_nonneg_right (by rw [hMdef]; linarith) (by positivity)
        _ = ρ' / 3 := by field_simp
    exact h1.trans h2
  refine ⟨ρ' / (3 * G.L), by positivity, δ' / 2, by positivity, r, by exact_mod_cast hr0, hrε,
    fun x hx ↦ ?_⟩
  obtain ⟨δx, hδx, κx, hκx, hlpsx⟩ :=
    G.lps {x} isCompact_singleton (Set.singleton_subset_iff.2 hx)
  have hκx0 : 0 < κx := by linarith
  set δ : ℝ := min δx (min (G.rLeaf / κx) (min (r / 4 / κx)
    (min (ρ' / (3 * (G.Cc + 1)) / κx) (δ' / 2 / (G.Cc * κx + 1))))) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδx' : δ ≤ δx := min_le_left _ _
  have hδr : κx * δ ≤ G.rLeaf := by
    have : δ ≤ G.rLeaf / κx := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hκx0, mul_comm] at this
  have hδq : κx * δ ≤ r / 4 := by
    have : δ ≤ r / 4 / κx :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rwa [le_div_iff₀ hκx0, mul_comm] at this
  have hδρ : G.Cc * (κx * δ) ≤ ρ' / 3 := by
    have : δ ≤ ρ' / (3 * (G.Cc + 1)) / κx :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ hκx0, mul_comm] at this
    have h1 : G.Cc * (κx * δ) ≤ G.Cc * (ρ' / (3 * (G.Cc + 1))) :=
      mul_le_mul_of_nonneg_left this hCc
    have h2 : G.Cc * (ρ' / (3 * (G.Cc + 1))) ≤ ρ' / 3 := by
      calc G.Cc * (ρ' / (3 * (G.Cc + 1))) ≤ (G.Cc + 1) * (ρ' / (3 * (G.Cc + 1))) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ρ' / 3 := by field_simp
    exact h1.trans h2
  have hδ'' : G.Cc * (κx * δ) < δ' / 2 := by
    have h2 : δ ≤ δ' / 2 / (G.Cc * κx + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    have h3 : G.Cc * (κx * δ) ≤ G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) < δ' / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hCc hκx0.le]
    exact h3.trans_lt h4
  refine ⟨δ, hδpos, fun kp hkp T hT i hi kq hkq ↦ ?_⟩
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  -- notation: `p`, `a = [x, p]_u`, `b = φ (-T) a`, `q`, `c = [q, b]_u`, `y = φ T c`
  set p := E.pIdx kp with hpdef
  set a := G.bracketU x p with hadef
  set b := G.φ (-(T : ℝ)) a with hbdef
  set q := E.pIdx kq with hqdef
  set c := G.bracketU q b with hcdef
  have hdxp : dist x p < δ := by rwa [dist_comm]
  have hdxp' : dist x p < δx := hdxp.trans_le hδx'
  have hinfx : ∃ q ∈ ({x} : Set _), dist x q < δx :=
    ⟨x, Set.mem_singleton x, by rw [dist_self]; exact hδx⟩
  obtain ⟨-, haW, hleg, haWs, hlegs, -⟩ := hlpsx x p hinfx hdxp'
  have hcu : G.dW .cu x a < κx * δ := lt_of_le_of_lt hleg (mul_lt_mul_of_pos_left hdxp hκx0)
  have hs : G.dW .s p a < κx * δ := lt_of_le_of_lt hlegs (mul_lt_mul_of_pos_left hdxp hκx0)
  have hcu_r : G.dW .cu x a < G.rLeaf := hcu.trans_le hδr
  have hbx : ∀ t : ℝ, 0 ≤ t → dist (G.φ (-t) a) (G.φ (-t) x) ≤ G.Cc * (κx * δ) := fun t ht ↦
    (G.center_leg_cu x a haW hcu_r t ht).trans (mul_le_mul_of_nonneg_left hcu.le hCc)
  have hbx' : dist b (G.φ (-(T : ℝ)) x) < δ' / 2 := (hbx T hT0).trans_lt hδ''
  have hinfq : ∃ q' ∈ Pm, dist q q' < δP := ⟨_, hT, hkq.trans_le (by linarith)⟩
  have hdqb : dist q b < δ' := by
    calc dist q b ≤ dist q (G.φ (-(T : ℝ)) x) + dist (G.φ (-(T : ℝ)) x) b := dist_triangle _ _ _
      _ < δ' / 2 + δ' / 2 := add_lt_add hkq (by rwa [dist_comm])
      _ = δ' := by ring
  obtain ⟨-, hcW, hlegc, hcWs, hlegcs, -⟩ := hlpsP q b hinfq (hdqb.trans_le hδ'P)
  have hc : G.dW .s b c < κP * δ' := lt_of_le_of_lt hlegcs (mul_lt_mul_of_pos_left hdqb hκP0)
  have hccu : G.dW .cu q c < κP * δ' :=
    lt_of_le_of_lt hlegc (mul_lt_mul_of_pos_left hdqb hκP0)
  have hab : G.φ (T : ℝ) b = a := by
    rw [hbdef, ← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have hyWa : G.φ (T : ℝ) c ∈ G.W .s a := by
    have := G.mem_W_flow hcWs (T : ℝ)
    rwa [hab] at this
  have hWap : G.W .s a = G.W .s p := G.W_eq_of_mem _ _ _ haWs
  have hyWp : G.φ (T : ℝ) c ∈ G.W .s p := by rwa [hWap] at hyWa
  have hdWay : G.dW .s a (G.φ (T : ℝ) c) ≤ G.dW .s b c := by
    have := G.dW_s_flow_le b c hcWs T hT0
    rwa [hab] at this
  refine ⟨?_, fun j hj ↦ ?_, fun n ↦ ?_⟩
  · refine (G.Kplaque'_spec p r (by exact_mod_cast hr0)).2.1 ⟨hyWp, ?_⟩
    calc G.dW .s p (G.φ (T : ℝ) c)
        ≤ G.dW .s p a + G.dW .s a (G.φ (T : ℝ) c) := G.dW_triangle _ _ _ _ haWs hyWp
      _ < κx * δ + κP * δ' := add_lt_add_of_lt_of_le hs (hdWay.trans hc.le)
      _ ≤ r / 4 + r / 4 := add_le_add hδq hδ'q
      _ = (r : ℝ) / 2 := by ring
  · have hj' : (j : ℝ) ≤ T := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hs0 : (0 : ℝ) ≤ (T : ℝ) - j := by linarith
    have e₁ : G.φ (-(j : ℝ)) (G.φ (T : ℝ) c) = G.φ ((T : ℝ) - j) c := by
      rw [← Flow.map_add]
      congr 1
      ring
    have e₂ : G.φ (-(j : ℝ)) a = G.φ ((T : ℝ) - j) b := by
      rw [hbdef, ← Flow.map_add]
      congr 1
      ring
    have hleaf : G.dW .s (G.φ (-(j : ℝ)) a) (G.φ (-(j : ℝ)) (G.φ (T : ℝ) c)) ≤ G.dW .s b c := by
      rw [e₁, e₂]
      exact G.dW_s_flow_le b c hcWs _ hs0
    have hmemj : G.φ (-(j : ℝ)) (G.φ (T : ℝ) c) ∈ G.W .s (G.φ (-(j : ℝ)) a) := by
      rw [e₁, e₂]
      exact G.mem_W_flow hcWs _
    have hA : dist (G.φ (-(j : ℝ)) a) (G.φ (-(j : ℝ)) (G.φ (T : ℝ) c)) ≤
        G.CLeaf * (κP * δ') := by
      have h1 := G.dist_le_CLeaf_mul_dW .s _ _ hmemj (hleaf.trans_lt (hc.trans_le hδ'r))
      exact h1.trans (mul_le_mul_of_nonneg_left (hleaf.trans hc.le) hCLeaf.le)
    have hB := hbx j hj0
    have hC : dist (G.φ (-(j : ℝ)) x) (G.φ (-(j : ℝ)) (P.ι i)) < G.L * (ρ' / (3 * G.L)) :=
      G.toFlowData.dist_flow_lt_of_mem_bowenBall_finv hi (neg_le_neg hj') (by linarith)
    have hC' : G.L * (ρ' / (3 * G.L)) = ρ' / 3 := by
      field_simp
    rw [hC'] at hC
    calc dist (G.φ (-(j : ℝ)) (G.φ (T : ℝ) c)) (G.φ (-(j : ℝ)) (P.ι i))
        ≤ dist (G.φ (-(j : ℝ)) (G.φ (T : ℝ) c)) (G.φ (-(j : ℝ)) a) +
            dist (G.φ (-(j : ℝ)) a) (G.φ (-(j : ℝ)) x) +
            dist (G.φ (-(j : ℝ)) x) (G.φ (-(j : ℝ)) (P.ι i)) := dist_triangle4 _ _ _ _
      _ ≤ ρ' / 3 + ρ' / 3 + ρ' / 3 := by
          rw [dist_comm (G.φ (-(j : ℝ)) (G.φ (T : ℝ) c))]
          exact add_le_add (add_le_add (hA.trans hδ'C) (hB.trans hδρ)) hC.le
      _ = ρ' := by ring
  · have e₃ : G.φ (-((T : ℝ) + n)) (G.φ (T : ℝ) c) = G.φ (-(n : ℝ)) c := by
      rw [← Flow.map_add]
      congr 1
      ring
    rw [e₃]
    have h1 := G.center_leg_cu q c hcW (hccu.trans_le hδ'r) n (Nat.cast_nonneg n)
    calc dist (G.φ (-(n : ℝ)) c) (G.φ (-(n : ℝ)) q) ≤ G.Cc * G.dW .cu q c := h1
      _ ≤ G.Cc * (κP * δ') := mul_le_mul_of_nonneg_left hccu.le hCc
      _ ≤ ρ' / 3 := hδ'Cc
      _ ≤ ρ' := by linarith

/-- The error of the backward bracket construction: `d^s(y, a) ≤ C' E₋(ρ)` with `a = [x,p]_u`,
by leafwise stable contraction (G5) along the backward orbit of `a` and the rate comparison
along the center unstable leg from `a` to `x`. Blueprint node `geo:bracket-approx` (reversed). -/
theorem bracket_construction_error_backward {Pm : Set X} (hPm : IsCompact Pm)
    (hPmR : Pm ⊆ G.Reg) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ η : ℝ, 0 < η ∧ ∀ x ∈ G.Reg, ∃ δ : ℝ, 0 < δ ∧
      ∀ kp, dist (E.pIdx kp) x < δ → ∀ T : ℕ, G.φ (-(T : ℝ)) x ∈ Pm →
        ∀ kq, dist (E.pIdx kq) (G.φ (-(T : ℝ)) x) < η →
          dist (G.φ (T : ℝ) (G.bracketU (E.pIdx kq) (G.φ (-(T : ℝ)) (G.bracketU x (E.pIdx kp)))))
              (G.bracketU x (E.pIdx kp)) ≤
            C' * G.scaleMinus ρ T x := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  set β : ℝ := ρ * Real.log 2 / 2 with hβdef
  have hβ : 0 < β := by positivity
  obtain ⟨δβ, hδβ, hcontr⟩ := G.dW_s_flow_le_of_accumulatedRateBackward β hβ
  obtain ⟨δacc, hδacc, hacc⟩ := G.accumulatedRateBackward_close_of_cu_leg β hβ
  obtain ⟨δP, hδP, κP, hκP, hlpsP⟩ := G.lps Pm hPm hPmR
  have hκP0 : 0 < κP := by linarith
  have hrLeaf := G.rLeaf_pos
  have hCc := G.Cc_nonneg
  have hCLeaf : 0 < G.CLeaf := by linarith [G.one_le_CLeaf]
  set δ' : ℝ := min δP (min (δβ / κP) (G.rLeaf / κP)) with hδ'def
  have hδ'pos : 0 < δ' := by positivity
  have hδ'P : δ' ≤ δP := min_le_left _ _
  have hδ'β : κP * δ' ≤ δβ := by
    have : δ' ≤ δβ / κP := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  have hδ'r : κP * δ' ≤ G.rLeaf := by
    have : δ' ≤ G.rLeaf / κP := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hκP0, mul_comm] at this
  refine ⟨G.CLeaf * κP * δ', by positivity, δ' / 2, by positivity, fun x hx ↦ ?_⟩
  obtain ⟨δx, hδx, κx, hκx, hlpsx⟩ :=
    G.lps {x} isCompact_singleton (Set.singleton_subset_iff.2 hx)
  have hκx0 : 0 < κx := by linarith
  set δ : ℝ := min δx (min (δacc / κx) (min (G.rLeaf / κx) (δ' / 2 / (G.Cc * κx + 1))))
    with hδdef
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, fun kp hkp T hT kq hkq ↦ ?_⟩
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  set p := E.pIdx kp with hpdef
  set a := G.bracketU x p with hadef
  set q := E.pIdx kq with hqdef
  have hdxp : dist x p < δ := by rwa [dist_comm]
  have hdxp' : dist x p < δx := hdxp.trans_le (min_le_left _ _)
  have hinfx : ∃ q ∈ ({x} : Set _), dist x q < δx :=
    ⟨x, Set.mem_singleton x, by rw [dist_self]; exact hδx⟩
  obtain ⟨-, haW, hleg, -, -, -⟩ := hlpsx x p hinfx hdxp'
  have hcu : G.dW .cu x a < κx * δ := lt_of_le_of_lt hleg (mul_lt_mul_of_pos_left hdxp hκx0)
  have hcu_acc : G.dW .cu x a < δacc := by
    have : δ ≤ δacc / κx := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ hκx0, mul_comm] at this
    exact hcu.trans_le this
  have hcu_r : G.dW .cu x a < G.rLeaf := by
    have : δ ≤ G.rLeaf / κx :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ hκx0, mul_comm] at this
    exact hcu.trans_le this
  have hbx : dist (G.φ (-(T : ℝ)) a) (G.φ (-(T : ℝ)) x) < δ' / 2 := by
    have h1 := G.center_leg_cu x a haW hcu_r T hT0
    have h2 : δ ≤ δ' / 2 / (G.Cc * κx + 1) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have h3 : G.Cc * (κx * δ) ≤ G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : G.Cc * κx * (δ' / 2 / (G.Cc * κx + 1)) < δ' / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hCc hκx0.le]
    calc dist (G.φ (-(T : ℝ)) a) (G.φ (-(T : ℝ)) x) ≤ G.Cc * G.dW .cu x a := h1
      _ ≤ G.Cc * (κx * δ) := mul_le_mul_of_nonneg_left hcu.le hCc
      _ < δ' / 2 := h3.trans_lt h4
  have hinfq : ∃ q' ∈ Pm, dist q q' < δP := ⟨_, hT, hkq.trans_le (by linarith)⟩
  have hdqb : dist q (G.φ (-(T : ℝ)) a) < δ' := by
    calc dist q (G.φ (-(T : ℝ)) a)
        ≤ dist q (G.φ (-(T : ℝ)) x) + dist (G.φ (-(T : ℝ)) x) (G.φ (-(T : ℝ)) a) :=
          dist_triangle _ _ _
      _ < δ' / 2 + δ' / 2 := add_lt_add hkq (by rwa [dist_comm])
      _ = δ' := by ring
  obtain ⟨-, -, -, hcWs, hlegs, -⟩ := hlpsP q (G.φ (-(T : ℝ)) a) hinfq (hdqb.trans_le hδ'P)
  have hc : G.dW .s (G.φ (-(T : ℝ)) a) (G.bracketU q (G.φ (-(T : ℝ)) a)) < κP * δ' :=
    lt_of_le_of_lt hlegs (mul_lt_mul_of_pos_left hdqb hκP0)
  have hab : G.φ (T : ℝ) (G.φ (-(T : ℝ)) a) = a := by
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  have h1 := hcontr a _ T hT0 hcWs (hc.trans_le hδ'β)
  have h2 := G.dW_s_flow_le _ _ hcWs T hT0
  rw [hab] at h2
  have hmem := G.mem_W_flow hcWs (T : ℝ)
  rw [hab] at hmem
  have hdist := G.dist_le_CLeaf_mul_dW .s _ _ hmem (h2.trans_lt (hc.trans_le hδ'r))
  have h3 := hacc x a haW hcu_acc T hT0
  have h4 : Real.exp (-(G.toFlowData.accumulatedRateBackward G.lamS T a - β * T)) ≤
      G.scaleMinus ρ T x := by
    rw [G.scaleMinus_eq_exp]
    apply Real.exp_le_exp.2
    have := (abs_le.1 h3).1
    have hβT : ρ * Real.log 2 * T = 2 * (β * T) := by rw [hβdef]; ring
    linarith
  rw [dist_comm]
  calc dist a (G.φ (T : ℝ) (G.bracketU q (G.φ (-(T : ℝ)) a)))
      ≤ G.CLeaf * G.dW .s a (G.φ (T : ℝ) (G.bracketU q (G.φ (-(T : ℝ)) a))) := hdist
    _ ≤ G.CLeaf * (G.dW .s (G.φ (-(T : ℝ)) a) (G.bracketU q (G.φ (-(T : ℝ)) a)) *
          Real.exp (-(G.toFlowData.accumulatedRateBackward G.lamS T a - β * T))) :=
        mul_le_mul_of_nonneg_left h1 hCLeaf.le
    _ ≤ G.CLeaf * ((κP * δ') * G.scaleMinus ρ T x) := by
        apply mul_le_mul_of_nonneg_left _ hCLeaf.le
        exact mul_le_mul hc.le h4 (Real.exp_pos _).le (by positivity)
    _ = G.CLeaf * κP * δ' * G.scaleMinus ρ T x := by ring

/-! ### `geo:bracket-approx`: uniqueness of the decoded point -/

/-- Uniqueness of the decoded point when the base point `pIdx kp` is near a point of a compact
regular set `Q` (a special case of `shadowSet_subsingleton` for the compact regular closed
thickening of `Q`). -/
theorem shadowSet_subsingleton_of_mem {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 ≤ ρ → 2 * G.L * ρ < a →
      ∀ x ∈ Q, ∀ kp, dist (E.pIdx kp) x < δ → ∀ r : ℚ, 0 < r → (r : ℝ) ≤ ε₀ →
        ∀ i T kq : ℕ, (E.shadowSet ρ r kp i T kq).Subsingleton := by
  obtain ⟨t, ht, htQ⟩ := hQ.exists_thickening_subset_open G.isOpen_Reg hQR
  have hQ' : IsCompact (Metric.cthickening (t / 2) Q) := hQ.cthickening
  have hQ'R : Metric.cthickening (t / 2) Q ⊆ G.Reg :=
    (Metric.cthickening_subset_thickening' ht (by linarith) Q).trans htQ
  obtain ⟨a, ha, ε₀, hε₀, h⟩ := E.shadowSet_subsingleton hQ' hQ'R
  refine ⟨a, ha, ε₀, hε₀, t / 2, by positivity, fun ρ hρ hρa x hx kp hkp r hr hrε i T kq ↦ ?_⟩
  exact h ρ hρ hρa kp r i T kq
    (Metric.mem_cthickening_of_dist_le _ _ _ _ hx hkp.le) ⟨hr, hrε⟩

/-- Backward counterpart of `shadowSet_subsingleton_of_mem`. -/
theorem shadowSetBackward_subsingleton_of_mem {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 ≤ ρ → 2 * G.L * ρ < a →
      ∀ x ∈ Q, ∀ kp, dist (E.pIdx kp) x < δ → ∀ r : ℚ, 0 < r → (r : ℝ) ≤ ε₀ →
        ∀ i T kq : ℕ, (E.shadowSetBackward ρ r kp i T kq).Subsingleton := by
  obtain ⟨t, ht, htQ⟩ := hQ.exists_thickening_subset_open G.isOpen_Reg hQR
  have hQ' : IsCompact (Metric.cthickening (t / 2) Q) := hQ.cthickening
  have hQ'R : Metric.cthickening (t / 2) Q ⊆ G.Reg :=
    (Metric.cthickening_subset_thickening' ht (by linarith) Q).trans htQ
  obtain ⟨a, ha, ε₀, hε₀, h⟩ := E.shadowSetBackward_subsingleton hQ' hQ'R
  refine ⟨a, ha, ε₀, hε₀, t / 2, by positivity, fun ρ hρ hρa x hx kp hkp r hr hrε i T kq ↦ ?_⟩
  exact h ρ hρ hρa kp r i T kq
    (Metric.mem_cthickening_of_dist_le _ _ _ _ hx hkp.le) ⟨hr, hrε⟩

end EffectiveGeodesicData

end Kolmogorov.PointToSet
