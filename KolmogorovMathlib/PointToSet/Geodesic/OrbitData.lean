/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.EffectiveData

/-!
# Orbit data (geodesic blueprint, Layer 3 abstraction)

An *orbit datum* for a point `x` under a map `T` is an ideal index `idx` together with the
number `order` of observed times and a tolerance `tol`, such that `P.ι idx` lies in the Bowen
ball `bowenBall T order x tol` (`OrbitDatum`). It is a proof object, never a program input: the
programs of Chapters E–H take the bare index `idx`, and their correctness statements quantify
over data of a given order and tolerance.

The file collects what the reconstruction argument reads off an orbit datum:

* the names of the flow at rational times along the ideal orbit, within `L · tol` of the
  orbit of `x` on the observed window (`OrbitDatum.names`, `OrbitDatum.names_backward`);
* the quadrature bounds for the unit potentials along the ideal orbit
  (`OrbitDatum.abs_birkhoff_sub_le`, `OrbitDatum.abs_birkhoff_sub_le_backward`);
* the computable integral scales `R₊ (d.idx, T)`, `R₋ (d.idx, T)` bracketing
  `scalePlus ρ T x`, `scaleMinus ρ T x` (`OrbitDatum.scalePlus`, `OrbitDatum.scaleMinus`);
* the finite orbit complexity as the minimum of `oracleNatComplexity A d.idx` over the data of
  a given order and tolerance (`orbitComplexityNat_le_idx`,
  `orbitComplexityNat_eq_iInf_orbitDatum`).

The integral scales `scalePlus`, `scaleMinus` themselves (decision D2 of Chapter E) are defined
here, since the computable scales need them. The earlier index-and-membership forms of the
names, the quadrature bounds and the computable scales were removed: a membership
`hi : P.ι i ∈ bowenBall T (n + 1) x ε` enters the datum forms as `OrbitDatum.ofMem hi`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-! ### Orbit data -/

/-- An orbit datum for `x`: an ideal index whose orbit under `T` shadows the orbit of `x` at
`order` observed times within tolerance `tol`. -/
structure OrbitDatum (P : Presentation X) (T : X → X) (x : X) where
  /-- The ideal index. -/
  idx : ℕ
  /-- The number of observed times (`T + 1` for the orbit on `[0, T]`). -/
  order : ℕ
  /-- The tolerance. -/
  tol : ℝ
  /-- The ideal point lies in the Bowen ball. -/
  mem : P.ι idx ∈ bowenBall T order x tol

namespace OrbitDatum

variable {P : Presentation X} {T : X → X} {x : X}

/-- The orbit datum read off a Bowen-ball membership. -/
def ofMem {i n : ℕ} {ε : ℝ} (h : P.ι i ∈ bowenBall T n x ε) : OrbitDatum P T x :=
  ⟨i, n, ε, h⟩

/-- The index of the datum read off a membership is the given index. -/
@[simp] theorem ofMem_idx {i n : ℕ} {ε : ℝ} (h : P.ι i ∈ bowenBall T n x ε) :
    (ofMem h).idx = i := rfl

/-- The order of the datum read off a membership is the given order. -/
@[simp] theorem ofMem_order {i n : ℕ} {ε : ℝ} (h : P.ι i ∈ bowenBall T n x ε) :
    (ofMem h).order = n := rfl

/-- The tolerance of the datum read off a membership is the given tolerance. -/
@[simp] theorem ofMem_tol {i n : ℕ} {ε : ℝ} (h : P.ι i ∈ bowenBall T n x ε) :
    (ofMem h).tol = ε := rfl

/-- An orbit datum is a datum at every lower order and every larger tolerance. -/
theorem mem_of_le (d : OrbitDatum P T x) {m : ℕ} {ε : ℝ} (hm : m ≤ d.order) (hε : d.tol ≤ ε) :
    P.ι d.idx ∈ bowenBall T m x ε :=
  bowenBall_subset_of_le T m x hε (Dynamics.dynEntourage_mono subset_rfl hm d.mem)

/-- Membership form of a datum of a given order, at a larger tolerance. -/
theorem mem_order (d : OrbitDatum P T x) {n : ℕ} {ε : ℝ} (hn : d.order = n) (hε : d.tol ≤ ε) :
    P.ι d.idx ∈ bowenBall T n x ε :=
  d.mem_of_le hn.ge hε

end OrbitDatum

/-! ### Orbit complexity as a minimum over orbit data -/

/-- The orbit complexity at the order and tolerance of a datum is at most the complexity of
its index. Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_le_idx {P : Presentation X} {T : X → X} (A : Set ℕ) {x : X}
    (d : OrbitDatum P T x) :
    orbitComplexityNat P T A x d.order d.tol ≤ oracleNatComplexity A d.idx :=
  orbitComplexityNat_le P T A x d.mem

/-- The finite orbit complexity is the minimum of `oracleNatComplexity A d.idx` over the orbit
data `d` of the given order and tolerance. Blueprint node `geo:orbit-complexity`. -/
theorem orbitComplexityNat_eq_iInf_orbitDatum (P : Presentation X) (T : X → X) (A : Set ℕ)
    (x : X) (hT : Continuous T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    orbitComplexityNat P T A x n ε =
      ⨅ d : {d : OrbitDatum P T x // d.order = n ∧ d.tol = ε}, oracleNatComplexity A d.1.idx := by
  obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A x hT n hε
  have : Nonempty {d : OrbitDatum P T x // d.order = n ∧ d.tol = ε} :=
    ⟨⟨⟨i, n, ε, hi⟩, rfl, rfl⟩⟩
  refine le_antisymm (le_ciInf fun d ↦ ?_) ?_
  · obtain ⟨d, hdn, hdε⟩ := d
    have h := orbitComplexityNat_le_idx A d
    rwa [hdn, hdε] at h
  · have h := ciInf_le (f := fun d : {d : OrbitDatum P T x // d.order = n ∧ d.tol = ε} ↦
      oracleNatComplexity A d.1.idx) (OrderBot.bddBelow _) ⟨⟨i, n, ε, hi⟩, rfl, rfl⟩
    rw [← hiK]
    exact h

variable [CompactSpace X]

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-! ### Integral scales -/

/-- The forward integral scale `E₊(ρ) = 2 ^ (-(S_T u⁺(x) - ρ T))`.
Blueprint nodes `geo:bracket-approx`, `geo:unit-potentials` (D2). -/
noncomputable def scalePlus (ρ : ℝ) (T : ℕ) (x : X) : ℝ :=
  (2 : ℝ) ^ (-(birkhoffSum G.f G.uPlus T x - ρ * T))

/-- The backward integral scale `E₋(ρ) = 2 ^ (-(S_T u⁻(x) - ρ T))`.
Blueprint nodes `geo:bracket-approx`, `geo:unit-potentials` (D2). -/
noncomputable def scaleMinus (ρ : ℝ) (T : ℕ) (x : X) : ℝ :=
  (2 : ℝ) ^ (-(birkhoffSum G.finv G.uMinus T x - ρ * T))

/-- Scales are positive. -/
theorem scalePlus_pos (ρ : ℝ) (T : ℕ) (x : X) : 0 < G.scalePlus ρ T x := by
  unfold scalePlus
  exact Real.rpow_pos_of_pos two_pos _

/-- Scales are positive. -/
theorem scaleMinus_pos (ρ : ℝ) (T : ℕ) (x : X) : 0 < G.scaleMinus ρ T x := by
  unfold scaleMinus
  exact Real.rpow_pos_of_pos two_pos _

/-- A smaller loss gives a smaller scale. -/
theorem scalePlus_mono_loss {ρ ρ' : ℝ} (h : ρ ≤ ρ') (T : ℕ) (x : X) :
    G.scalePlus ρ T x ≤ G.scalePlus ρ' T x := by
  unfold scalePlus
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) T)
  linarith

/-- A smaller loss gives a smaller scale. -/
theorem scaleMinus_mono_loss {ρ ρ' : ℝ} (h : ρ ≤ ρ') (T : ℕ) (x : X) :
    G.scaleMinus ρ T x ≤ G.scaleMinus ρ' T x := by
  unfold scaleMinus
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) T)
  linarith

/-- The natural-exponential form of the drafts: `E₊(ρ) = exp (-(∫₀ᵀ λᵘ(φ τ x) dτ - ρ' T))` with
`ρ' = ρ log 2`. Blueprint decision D2. -/
theorem scalePlus_eq_exp (ρ : ℝ) (T : ℕ) (x : X) :
    G.scalePlus ρ T x =
      Real.exp (-(G.toFlowData.accumulatedRate G.lamU T x - ρ * Real.log 2 * T)) := by
  have hS := G.toFlowData.birkhoffSum_unitPotential G.continuous_lamU T x
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hacc : G.toFlowData.accumulatedRate G.lamU T x =
      Real.log 2 * birkhoffSum G.f G.uPlus T x := by
    unfold uPlus
    rw [hS]
    field_simp
  unfold scalePlus
  rw [Real.rpow_def_of_pos two_pos, hacc]
  congr 1
  ring

/-- The backward form of `scalePlus_eq_exp`:
`E₋(ρ) = exp (-(∫₀ᵀ λˢ(φ (-τ) x) dτ - ρ' T))` with `ρ' = ρ log 2`. -/
theorem scaleMinus_eq_exp (ρ : ℝ) (T : ℕ) (x : X) :
    G.scaleMinus ρ T x =
      Real.exp (-(G.toFlowData.accumulatedRateBackward G.lamS T x - ρ * Real.log 2 * T)) := by
  have hS := G.toFlowData.birkhoffSum_unitPotentialBackward G.continuous_lamS T x
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hacc : G.toFlowData.accumulatedRateBackward G.lamS T x =
      Real.log 2 * birkhoffSum G.finv G.uMinus T x := by
    unfold uMinus
    rw [hS]
    field_simp
  unfold scaleMinus
  rw [Real.rpow_def_of_pos two_pos, hacc]
  congr 1
  ring

/-- Backward Birkhoff transfer along a center unstable leg: the backward accumulated stable
rates of `a ∈ W^{cu}_δ(x)` and `x` differ by at most `ρ T` on `[0, T]` (mirror of
`accumulatedRate_close_of_cs_leg`, from `lamS_flow_close_of_cu_leg`). -/
theorem accumulatedRateBackward_close_of_cu_leg (ρ : ℝ) (hρ : 0 < ρ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x a : X, a ∈ G.W .cu x → G.dW .cu x a < δ → ∀ T : ℝ, 0 ≤ T →
      |G.toFlowData.accumulatedRateBackward G.lamS T a -
        G.toFlowData.accumulatedRateBackward G.lamS T x| ≤ ρ * T := by
  obtain ⟨δ, hδ, h⟩ := G.lamS_flow_close_of_cu_leg ρ hρ
  refine ⟨δ, hδ, fun x a ha hd T hT ↦ ?_⟩
  have hca : Continuous fun τ : ℝ ↦ G.lamS (G.φ (-τ) a) :=
    G.continuous_lamS.comp (G.φ.continuous continuous_neg continuous_const)
  have hcx : Continuous fun τ : ℝ ↦ G.lamS (G.φ (-τ) x) :=
    G.continuous_lamS.comp (G.φ.continuous continuous_neg continuous_const)
  unfold FlowData.accumulatedRateBackward
  rw [← intervalIntegral.integral_sub (hca.intervalIntegrable 0 T) (hcx.intervalIntegrable 0 T)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := ρ)
    (f := fun τ ↦ G.lamS (G.φ (-τ) a) - G.lamS (G.φ (-τ) x)) ?_
  · simpa [Real.norm_eq_abs, abs_of_nonneg hT] using hb
  · intro τ hτ
    rw [Set.uIoc_of_le hT] at hτ
    rw [Real.norm_eq_abs]
    exact (h x a ha hd τ hτ.1.le).le

/-- The numerical rounding error `2 ^ (-(Λ' + 1) T)` is at most the scale, where
`Λ' = Λ / log 2` bounds `u⁺` (used to round the decoder output). -/
theorem two_zpow_neg_le_scalePlus (ρ : ℝ) (hρ : 0 ≤ ρ) (T : ℕ) (x : X) :
    (2 : ℝ) ^ (-((G.Λ / Real.log 2 + 1) * T)) ≤ G.scalePlus ρ T x := by
  unfold scalePlus
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  have hb : birkhoffSum G.f G.uPlus T x ≤ (G.Λ / Real.log 2) * T := by
    have hle := G.uPlus_props.2.2
    unfold birkhoffSum
    calc ∑ k ∈ Finset.range T, G.uPlus (G.f^[k] x)
        ≤ ∑ _k ∈ Finset.range T, G.Λ / Real.log 2 := Finset.sum_le_sum fun k _ ↦ hle _
      _ = (G.Λ / Real.log 2) * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hρT : 0 ≤ ρ * T := mul_nonneg hρ (Nat.cast_nonneg T)
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  linarith

/-- The backward counterpart of `two_zpow_neg_le_scalePlus`. -/
theorem two_zpow_neg_le_scaleMinus (ρ : ℝ) (hρ : 0 ≤ ρ) (T : ℕ) (x : X) :
    (2 : ℝ) ^ (-((G.Λ / Real.log 2 + 1) * T)) ≤ G.scaleMinus ρ T x := by
  unfold scaleMinus
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  have hb : birkhoffSum G.finv G.uMinus T x ≤ (G.Λ / Real.log 2) * T := by
    have hle := G.uMinus_props.2.2
    unfold birkhoffSum
    calc ∑ k ∈ Finset.range T, G.uMinus (G.finv^[k] x)
        ≤ ∑ _k ∈ Finset.range T, G.Λ / Real.log 2 := Finset.sum_le_sum fun k _ ↦ hle _
      _ = (G.Λ / Real.log 2) * T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hρT : 0 ≤ ρ * T := mul_nonneg hρ (Nat.cast_nonneg T)
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  linarith

/-- The dyadic radius `2 ^ (-n)` as a real power. -/
theorem dyadicRadius_eq_rpow (n : ℕ) : dyadicRadius n = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [dyadicRadius, Real.rpow_neg zero_le_two, Real.rpow_natCast, inv_pow]

/-- A computable precision scheme dominated by the forward scale: with a natural
`N ≥ Λ / log 2 + 1`, the dyadic radius at precision `N T` is at most `E₊(ρ)`. -/
theorem exists_nat_dyadicRadius_le_scalePlus {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ N : ℕ, ∀ (T : ℕ) (x : X), dyadicRadius (N * T) ≤ G.scalePlus ρ T x := by
  obtain ⟨N, hN⟩ := exists_nat_ge (G.Λ / Real.log 2 + 1)
  refine ⟨N, fun T x ↦ ?_⟩
  rw [dyadicRadius_eq_rpow]
  refine le_trans ?_ (G.two_zpow_neg_le_scalePlus ρ hρ T x)
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have := mul_le_mul_of_nonneg_right hN hT
  push_cast
  linarith

/-- Backward counterpart of `exists_nat_dyadicRadius_le_scalePlus`. -/
theorem exists_nat_dyadicRadius_le_scaleMinus {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ N : ℕ, ∀ (T : ℕ) (x : X), dyadicRadius (N * T) ≤ G.scaleMinus ρ T x := by
  obtain ⟨N, hN⟩ := exists_nat_ge (G.Λ / Real.log 2 + 1)
  refine ⟨N, fun T x ↦ ?_⟩
  rw [dyadicRadius_eq_rpow]
  refine le_trans ?_ (G.two_zpow_neg_le_scaleMinus ρ hρ T x)
  apply Real.rpow_le_rpow_of_exponent_le one_le_two
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have := mul_le_mul_of_nonneg_right hN hT
  push_cast
  linarith

end GeodesicReconstructionData

namespace OrbitDatum

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}

/-! ### Names along an orbit datum -/

/-- Along a forward orbit datum of order `n + 1`, the flow at every rational time `q ∈ [0, n]`
has a computable name uniformly in `(q, p)`, and it approximates `φ q x` within `L · tol`. This
is how "an orbit description at tolerance `ε`" of OTL §1 is read off a Bowen-ball ideal point.
Blueprint nodes `geo:effective-data`, `geo:bowen-flow-compare`. -/
theorem names (E : EffectiveGeodesicData G P B) {x : X} {n : ℕ} (d : OrbitDatum P G.f x)
    (hd : d.order = n + 1) :
    ∃ b : ℚ → ℕ → ℕ, ComputableIn {charOracle B} (fun qp : ℚ × ℕ ↦ b qp.1 qp.2) ∧
      ∀ q : ℚ, IsCauchyName P (G.φ (q : ℝ) (P.ι d.idx)) (b q) ∧
        (0 ≤ q → (q : ℝ) ≤ n →
          dist (G.φ (q : ℝ) x) (G.φ (q : ℝ) (P.ι d.idx)) < G.L * d.tol) := by
  obtain ⟨b, hb, hname⟩ := IsRepresentedFamilyIn.names P P B E.presentation E.flow_represented
    (isCauchyName_const P d.idx) (ComputableIn.const d.idx)
  refine ⟨b, hb, fun q ↦ ⟨hname q, fun h0 hn ↦ ?_⟩⟩
  exact G.toFlowData.dist_flow_lt_of_mem_bowenBall (d.mem_order hd le_rfl)
    (by exact_mod_cast h0) hn

/-- Names along a backward orbit datum (an `finv`-Bowen ball): the flow at the rational times
`-q`, `q ∈ [0, n]`. -/
theorem names_backward (E : EffectiveGeodesicData G P B) {x : X} {n : ℕ}
    (d : OrbitDatum P G.finv x) (hd : d.order = n + 1) :
    ∃ b : ℚ → ℕ → ℕ, ComputableIn {charOracle B} (fun qp : ℚ × ℕ ↦ b qp.1 qp.2) ∧
      ∀ q : ℚ, IsCauchyName P (G.φ (-(q : ℝ)) (P.ι d.idx)) (b q) ∧
        (0 ≤ q → (q : ℝ) ≤ n →
          dist (G.φ (-(q : ℝ)) x) (G.φ (-(q : ℝ)) (P.ι d.idx)) < G.L * d.tol) := by
  obtain ⟨b, hb, hname⟩ := IsRepresentedFamilyIn.names P P B E.presentation E.flow_represented
    (isCauchyName_const P d.idx) (ComputableIn.const d.idx)
  refine ⟨fun q ↦ b (-q), ?_, fun q ↦ ⟨?_, fun h0 hn ↦ ?_⟩⟩
  · exact hb.comp
      ((ComputableReals.computable_ratNeg.comp Computable.fst).pair Computable.snd).computableIn
  · have h := hname (-q)
    rwa [Rat.cast_neg] at h
  · have h0' : (0 : ℝ) ≤ q := by exact_mod_cast h0
    exact G.toFlowData.dist_flow_lt_of_mem_bowenBall_finv (d.mem_order hd le_rfl)
      (neg_le_neg hn) (neg_nonpos.mpr h0')

/-! ### Quadrature along an orbit datum -/

/-- Quadrature along a forward orbit datum: for every `ρ > 0` there is a tolerance `ε` such
that the Birkhoff sum of `u⁺` at the ideal point of a datum of order `T + 1` and tolerance at
most `ε` differs from `S_T u⁺(x)` by at most `ρ T / 4` (through the oscillation modulus of
`u⁺`, library `small_scale_oscillation_birkhoff`).
Blueprint node `geo:effective-neighborhoods`. -/
theorem abs_birkhoff_sub_le {ρ : ℝ} (hρ : 0 < ρ) : ∃ ε : ℝ, 0 < ε ∧
    ∀ (x : X) (T : ℕ) (d : OrbitDatum P G.f x), d.order = T + 1 → d.tol ≤ ε →
      |birkhoffSum G.f G.uPlus T (P.ι d.idx) - birkhoffSum G.f G.uPlus T x| ≤ ρ * T / 4 := by
  obtain ⟨ω, -, hωlim, p₀, hp₀⟩ := small_scale_oscillation G.uPlus G.uPlus_props.1
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp
    (hωlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < ρ / 4)))
  refine ⟨dyadicRadius (max p₀ p₁), dyadicRadius_pos _, fun x T d hdT hdtol ↦ ?_⟩
  have hi := d.mem_order hdT hdtol
  have h1 := small_scale_oscillation_birkhoff G.f G.uPlus (max p₀ p₁) (ω (max p₀ p₁))
    (hp₀ _ (le_max_left _ _)) T x (P.ι d.idx) (bowen_ball_dense_succ G.f T x _ hi)
  have h2 := hp₁ _ (le_max_right p₀ p₁)
  calc _ ≤ (T : ℝ) * ω (max p₀ p₁) := h1
    _ ≤ (T : ℝ) * (ρ / 4) := by gcongr
    _ = ρ * T / 4 := by ring

/-- Quadrature along a backward orbit datum. Blueprint node `geo:effective-neighborhoods`. -/
theorem abs_birkhoff_sub_le_backward {ρ : ℝ} (hρ : 0 < ρ) : ∃ ε : ℝ, 0 < ε ∧
    ∀ (x : X) (T : ℕ) (d : OrbitDatum P G.finv x), d.order = T + 1 → d.tol ≤ ε →
      |birkhoffSum G.finv G.uMinus T (P.ι d.idx) - birkhoffSum G.finv G.uMinus T x| ≤
        ρ * T / 4 := by
  obtain ⟨ω, -, hωlim, p₀, hp₀⟩ := small_scale_oscillation G.uMinus G.uMinus_props.1
  obtain ⟨p₁, hp₁⟩ := eventually_atTop.mp
    (hωlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < ρ / 4)))
  refine ⟨dyadicRadius (max p₀ p₁), dyadicRadius_pos _, fun x T d hdT hdtol ↦ ?_⟩
  have hi := d.mem_order hdT hdtol
  have h1 := small_scale_oscillation_birkhoff G.finv G.uMinus (max p₀ p₁) (ω (max p₀ p₁))
    (hp₀ _ (le_max_left _ _)) T x (P.ι d.idx) (bowen_ball_dense_succ G.finv T x _ hi)
  have h2 := hp₁ _ (le_max_right p₀ p₁)
  calc _ ≤ (T : ℝ) * ω (max p₀ p₁) := h1
    _ ≤ (T : ℝ) * (ρ / 4) := by gcongr
    _ = ρ * T / 4 := by ring

/-! ### Computable scales from effective quadrature -/

/-- The computable forward scale: one `B`-computable rational function `R₊ (i, T)` with
`E₊(ρ/2) ≤ R₊ (d.idx, T) ≤ E₊(ρ)` for every forward orbit datum `d` of order `T + 1` and
tolerance at most `ε`. It is `2 ^ (-(Ŝ - 3ρT/4))` for a rational approximation `Ŝ` of the
Birkhoff sum at `ι d.idx`, rounded so that both inequalities survive. For `T = 0` the value is
`1`. Blueprint node `geo:effective-neighborhoods`. -/
theorem scalePlus (E : EffectiveGeodesicData G P B) (ρ : ℚ) (hρ : 0 < ρ) : ∃ ε : ℝ, 0 < ε ∧
    ∃ Rp : ℕ × ℕ → ℚ, ComputableIn {charOracle B} Rp ∧
      ∀ (x : X) (T : ℕ) (d : OrbitDatum P G.f x), d.order = T + 1 → d.tol ≤ ε →
        0 < Rp (d.idx, T) ∧ G.scalePlus (ρ / 2) T x ≤ Rp (d.idx, T) ∧
          (Rp (d.idx, T) : ℝ) ≤ G.scalePlus ρ T x := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  obtain ⟨ε, hε, hosc⟩ :=
    OrbitDatum.abs_birkhoff_sub_le (G := G) (P := P) (ρ := (ρ : ℝ) / 4)
      (by positivity)
  obtain ⟨q, hq, hqerr⟩ := E.birkhoff_uPlus_computable
  obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ρ / 16 by positivity)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  -- rational exponent bounds
  obtain ⟨lo, hlo_def⟩ : ∃ lo : ℕ × ℕ → ℚ, lo = fun d ↦ 5 * ρ / 8 * (d.2 : ℚ) - q (d, p₀) :=
    ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi : ℕ × ℕ → ℚ, hi = fun d ↦ 7 * ρ / 8 * (d.2 : ℚ) - q (d, p₀) :=
    ⟨_, rfl⟩
  -- exact rational comparison with `2 ^ a`
  have h2a : ∀ a : ℚ, ((2 : ℝ) ^ (a : ℝ)) ^ a.den = (2 : ℝ) ^ a.num := by
    intro a
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
    congr 1
    exact_mod_cast a.mul_den_eq_num
  have hcast2 : ∀ a : ℚ, (((2 : ℚ) ^ a.num : ℚ) : ℝ) = (2 : ℝ) ^ a.num := by
    intro a
    rw [Rat.cast_zpow]
    norm_num
  have hkey : ∀ (a r : ℚ), 0 < r →
      ((2 : ℝ) ^ (a : ℝ) < r ↔ (2 : ℚ) ^ a.num < r ^ a.den) := by
    intro a r hr
    rw [← pow_lt_pow_iff_left₀ (by positivity) (Rat.cast_pos.mpr hr).le a.den_nz, h2a,
      ← hcast2, ← Rat.cast_pow]
    exact Rat.cast_lt
  have hkey' : ∀ (a r : ℚ), 0 < r →
      ((r : ℝ) < (2 : ℝ) ^ (a : ℝ) ↔ r ^ a.den < (2 : ℚ) ^ a.num) := by
    intro a r hr
    rw [← pow_lt_pow_iff_left₀ (Rat.cast_pos.mpr hr).le (by positivity) a.den_nz, h2a,
      ← hcast2, ← Rat.cast_pow]
    exact Rat.cast_lt
  -- computability of the ingredients
  have hpow2 : Primrec fun n : ℕ ↦ 2 ^ n := by
    have h : Primrec fun n : ℕ ↦ (Nat.rec (1 : ℕ) (fun _ ih ↦ 2 * ih) n : ℕ) :=
      Primrec.nat_rec₁ (f := fun _ ih ↦ 2 * ih) 1
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
    refine h.of_eq fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← ih]
  have hzpow : Computable fun z : ℤ ↦ (2 : ℚ) ^ z := by
    refine computable_of_num_den (N := fun z : ℤ ↦ ((2 ^ z.toNat : ℕ) : ℤ))
      (D := fun z : ℤ ↦ 2 ^ (-z).toNat)
      (ComputableReals.primrec_natCastInt.to_comp.comp
        (hpow2.to_comp.comp ComputableReals.primrec_intToNat.to_comp))
      (hpow2.to_comp.comp ComputableReals.primrec_intNegToNat.to_comp)
      (fun _ ↦ pow_pos (by norm_num) _) (fun z ↦ ?_)
    cases z with
    | ofNat n => simp
    | negSucc n => simp [zpow_negSucc, Int.neg_negSucc]
  have hratpow : Computable fun p : ℚ × ℕ ↦ p.1 ^ p.2 := by
    have h : Computable fun p : ℚ × ℕ ↦ (Nat.rec (1 : ℚ) (fun _ ih ↦ p.1 * ih) p.2 : ℚ) :=
      Computable.nat_rec (f := fun p : ℚ × ℕ ↦ p.2) (g := fun _ ↦ (1 : ℚ))
        (h := fun p y ↦ p.1 * y.2) Computable.snd (Computable.const 1)
        (computable₂_ratMul.comp (Computable.fst.comp Computable.fst)
          (Computable.snd.comp Computable.snd))
    refine h.of_eq fun p ↦ ?_
    obtain ⟨r, n⟩ := p
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← ih]
  have hS : ComputableIn {charOracle B} fun d : ℕ × ℕ ↦ q (d, p₀) :=
    (hq.comp (Computable.id.pair (Computable.const p₀)).computableIn).of_eq fun _ ↦ rfl
  have hTq : Computable fun d : ℕ × ℕ ↦ (d.2 : ℚ) :=
    ComputableReals.computable_natCastRat.comp Computable.snd
  have hlo : ComputableIn {charOracle B} lo := by
    rw [hlo_def]
    exact computable₂_ratSub.computableIn₂.comp
      (computable₂_ratMul.comp (Computable.const (5 * ρ / 8)) hTq).computableIn hS
  have hhi : ComputableIn {charOracle B} hi := by
    rw [hhi_def]
    exact computable₂_ratSub.computableIn₂.comp
      (computable₂_ratMul.comp (Computable.const (7 * ρ / 8)) hTq).computableIn hS
  have hr : Computable fun dn : (ℕ × ℕ) × ℕ ↦ Denumerable.ofNat ℚ dn.2 :=
    (Computable.ofNat ℚ).comp Computable.snd
  have hlo' : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ lo dn.1 :=
    hlo.comp ComputableIn.fst
  have hhi' : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ hi dn.1 :=
    hhi.comp ComputableIn.fst
  have hA : Computable fun dn : (ℕ × ℕ) × ℕ ↦ decide (0 < Denumerable.ofNat ℚ dn.2) :=
    computable₂_ratLt.comp (Computable.const 0) hr
  have hpowlo : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      (Denumerable.ofNat ℚ dn.2) ^ (lo dn.1).den :=
    (hratpow.computableIn.comp
      (hr.computableIn.pair (computable_ratDen.computableIn.comp hlo'))).of_eq fun _ ↦ rfl
  have hpowhi : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      (Denumerable.ofNat ℚ dn.2) ^ (hi dn.1).den :=
    (hratpow.computableIn.comp
      (hr.computableIn.pair (computable_ratDen.computableIn.comp hhi'))).of_eq fun _ ↦ rfl
  have hzlo : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ (2 : ℚ) ^ (lo dn.1).num :=
    (hzpow.computableIn.comp (computable_ratNum.computableIn.comp hlo')).of_eq fun _ ↦ rfl
  have hzhi : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ (2 : ℚ) ^ (hi dn.1).num :=
    (hzpow.computableIn.comp (computable_ratNum.computableIn.comp hhi')).of_eq fun _ ↦ rfl
  have hB : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      decide ((2 : ℚ) ^ (lo dn.1).num < (Denumerable.ofNat ℚ dn.2) ^ (lo dn.1).den) :=
    computable₂_ratLt.computableIn₂.comp hzlo hpowlo
  have hC : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      decide ((Denumerable.ofNat ℚ dn.2) ^ (hi dn.1).den < (2 : ℚ) ^ (hi dn.1).num) :=
    computable₂_ratLt.computableIn₂.comp hpowhi hzhi
  have hand : Computable₂ fun a b : Bool ↦ (a && b) := (Primrec.dom_bool₂ _).to_comp
  obtain ⟨test, htest_def⟩ : ∃ test : (ℕ × ℕ) × ℕ → Bool, test = fun dn ↦
      decide (0 < Denumerable.ofNat ℚ dn.2 ∧
        (2 : ℚ) ^ (lo dn.1).num < (Denumerable.ofNat ℚ dn.2) ^ (lo dn.1).den ∧
        (Denumerable.ofNat ℚ dn.2) ^ (hi dn.1).den < (2 : ℚ) ^ (hi dn.1).num) := ⟨_, rfl⟩
  have htest : ComputableIn {charOracle B} test := by
    rw [htest_def]
    refine (hand.computableIn₂.comp hA.computableIn (hand.computableIn₂.comp hB hC)).of_eq
      fun dn ↦ ?_
    simp only [Bool.decide_and]
  -- the search and the total program
  have hsearch : PartrecIn {charOracle B} fun d : ℕ × ℕ ↦
      Nat.rfind fun n ↦ (Part.some (test (d, n)) : Part Bool) :=
    PartrecIn.rfind (p := fun d n ↦ (Part.some (test (d, n)) : Part Bool))
      (ComputableIn₂.mk (f := fun d n ↦ test (d, n)) htest).partrecIn₂
  have hc : ComputableIn {charOracle B} fun d : ℕ × ℕ ↦ decide (d.2 = 0) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (Primrec.const 0))).to_comp.computableIn
  obtain ⟨Rpart, hRpart_def⟩ : ∃ Rpart : ℕ × ℕ →. ℚ, Rpart = fun d ↦
      bif decide (d.2 = 0) then Part.some (1 : ℚ) else
        (Nat.rfind fun n ↦ (Part.some (test (d, n)) : Part Bool)).map (Denumerable.ofNat ℚ) :=
    ⟨_, rfl⟩
  have hRpart : PartrecIn {charOracle B} Rpart := by
    rw [hRpart_def]
    exact PartrecIn.cond hc (ComputableIn.const (1 : ℚ)).partrecIn
      (hsearch.map ((Computable.ofNat ℚ).comp Computable.snd).computableIn)
  have hdom : ∀ d, (Rpart d).Dom := by
    intro d
    rw [hRpart_def]
    by_cases hT : d.2 = 0
    · simp [hT]
    · have hT' : (1 : ℝ) ≤ d.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
      have hlt : ((lo d : ℚ) : ℝ) < hi d := by
        rw [hlo_def, hhi_def]
        push_cast
        nlinarith
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (Real.rpow_lt_rpow_of_exponent_lt one_lt_two hlt)
      have hrpos : 0 < r := by exact_mod_cast (Real.rpow_pos_of_pos two_pos _).trans hr1
      obtain ⟨n, hn⟩ : ∃ n, Denumerable.ofNat ℚ n = r := ⟨_, Denumerable.ofNat_encode r⟩
      have ht : test (d, n) = true := by
        rw [htest_def]
        simp only [decide_eq_true_iff]
        rw [hn]
        exact ⟨hrpos, (hkey _ _ hrpos).mp hr1, (hkey' _ _ hrpos).mp hr2⟩
      simp only [hT, decide_false, Bool.cond_false, Part.map_Dom]
      exact Nat.rfind_dom.mpr ⟨n, Part.mem_some_iff.mpr ht.symm, fun _ ↦ trivial⟩
  refine ⟨ε, hε, fun d ↦ (Rpart d).get (hdom d),
    PartrecIn.of_eq_tot hRpart fun d ↦ Part.get_mem (hdom d), fun x T d hdT hdtol ↦ ?_⟩
  have hi' := d.mem_order hdT hdtol
  generalize d.idx = i at hi' ⊢
  have hS := hosc x T (OrbitDatum.ofMem hi') rfl le_rfl
  simp only [OrbitDatum.ofMem_idx] at hS
  have hq1 := hqerr (i, T) p₀
  dsimp only at hq1 ⊢
  by_cases hT : T = 0
  · subst hT
    have hR : (Rpart (i, 0)).get (hdom (i, 0)) = 1 := by
      simp [hRpart_def]
    rw [hR]
    simp [GeodesicReconstructionData.scalePlus, birkhoffSum_zero_apply]
  · have hT' : (1 : ℝ) ≤ T := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
    have hmem0 : (Rpart (i, T)).get (hdom (i, T)) ∈ Rpart (i, T) := Part.get_mem _
    generalize (Rpart (i, T)).get (hdom (i, T)) = r at hmem0 ⊢
    have hmem := hmem0
    rw [hRpart_def] at hmem
    simp only [hT, decide_false, Bool.cond_false, Part.mem_map_iff] at hmem
    obtain ⟨n, hn, hrn⟩ := hmem
    have ht : test ((i, T), n) = true := (Part.mem_some_iff.mp (Nat.rfind_spec hn)).symm
    rw [htest_def] at ht
    simp only [decide_eq_true_iff] at ht
    rw [hrn] at ht
    obtain ⟨hrpos, hlo1, hhi1⟩ := ht
    have hab1 := abs_le.mp hS
    have hab2 := abs_lt.mp hq1
    have hρT : (ρ : ℝ) ≤ ρ * T := by nlinarith
    refine ⟨hrpos, ?_, ?_⟩
    · refine le_trans ?_ ((hkey _ _ hrpos).mpr hlo1).le
      unfold GeodesicReconstructionData.scalePlus
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [hlo_def]
      push_cast
      linarith
    · refine ((hkey' _ _ hrpos).mpr hhi1).le.trans ?_
      unfold GeodesicReconstructionData.scalePlus
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [hhi_def]
      push_cast
      linarith

/-- The computable backward scale, for backward orbit data.
Blueprint node `geo:effective-neighborhoods`. -/
theorem scaleMinus (E : EffectiveGeodesicData G P B) (ρ : ℚ) (hρ : 0 < ρ) : ∃ ε : ℝ, 0 < ε ∧
    ∃ Rm : ℕ × ℕ → ℚ, ComputableIn {charOracle B} Rm ∧
      ∀ (x : X) (T : ℕ) (d : OrbitDatum P G.finv x), d.order = T + 1 → d.tol ≤ ε →
        0 < Rm (d.idx, T) ∧ G.scaleMinus (ρ / 2) T x ≤ Rm (d.idx, T) ∧
          (Rm (d.idx, T) : ℝ) ≤ G.scaleMinus ρ T x := by
  have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
  obtain ⟨ε, hε, hosc⟩ :=
    OrbitDatum.abs_birkhoff_sub_le_backward (G := G) (P := P) (ρ := (ρ : ℝ) / 4)
      (by positivity)
  obtain ⟨q, hq, hqerr⟩ := E.birkhoff_uMinus_computable
  obtain ⟨p₀, hp₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ρ / 16 by positivity)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  -- rational exponent bounds
  obtain ⟨lo, hlo_def⟩ : ∃ lo : ℕ × ℕ → ℚ, lo = fun d ↦ 5 * ρ / 8 * (d.2 : ℚ) - q (d, p₀) :=
    ⟨_, rfl⟩
  obtain ⟨hi, hhi_def⟩ : ∃ hi : ℕ × ℕ → ℚ, hi = fun d ↦ 7 * ρ / 8 * (d.2 : ℚ) - q (d, p₀) :=
    ⟨_, rfl⟩
  -- exact rational comparison with `2 ^ a`
  have h2a : ∀ a : ℚ, ((2 : ℝ) ^ (a : ℝ)) ^ a.den = (2 : ℝ) ^ a.num := by
    intro a
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast]
    congr 1
    exact_mod_cast a.mul_den_eq_num
  have hcast2 : ∀ a : ℚ, (((2 : ℚ) ^ a.num : ℚ) : ℝ) = (2 : ℝ) ^ a.num := by
    intro a
    rw [Rat.cast_zpow]
    norm_num
  have hkey : ∀ (a r : ℚ), 0 < r →
      ((2 : ℝ) ^ (a : ℝ) < r ↔ (2 : ℚ) ^ a.num < r ^ a.den) := by
    intro a r hr
    rw [← pow_lt_pow_iff_left₀ (by positivity) (Rat.cast_pos.mpr hr).le a.den_nz, h2a,
      ← hcast2, ← Rat.cast_pow]
    exact Rat.cast_lt
  have hkey' : ∀ (a r : ℚ), 0 < r →
      ((r : ℝ) < (2 : ℝ) ^ (a : ℝ) ↔ r ^ a.den < (2 : ℚ) ^ a.num) := by
    intro a r hr
    rw [← pow_lt_pow_iff_left₀ (Rat.cast_pos.mpr hr).le (by positivity) a.den_nz, h2a,
      ← hcast2, ← Rat.cast_pow]
    exact Rat.cast_lt
  -- computability of the ingredients
  have hpow2 : Primrec fun n : ℕ ↦ 2 ^ n := by
    have h : Primrec fun n : ℕ ↦ (Nat.rec (1 : ℕ) (fun _ ih ↦ 2 * ih) n : ℕ) :=
      Primrec.nat_rec₁ (f := fun _ ih ↦ 2 * ih) 1
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
    refine h.of_eq fun n ↦ ?_
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← ih]
  have hzpow : Computable fun z : ℤ ↦ (2 : ℚ) ^ z := by
    refine computable_of_num_den (N := fun z : ℤ ↦ ((2 ^ z.toNat : ℕ) : ℤ))
      (D := fun z : ℤ ↦ 2 ^ (-z).toNat)
      (ComputableReals.primrec_natCastInt.to_comp.comp
        (hpow2.to_comp.comp ComputableReals.primrec_intToNat.to_comp))
      (hpow2.to_comp.comp ComputableReals.primrec_intNegToNat.to_comp)
      (fun _ ↦ pow_pos (by norm_num) _) (fun z ↦ ?_)
    cases z with
    | ofNat n => simp
    | negSucc n => simp [zpow_negSucc, Int.neg_negSucc]
  have hratpow : Computable fun p : ℚ × ℕ ↦ p.1 ^ p.2 := by
    have h : Computable fun p : ℚ × ℕ ↦ (Nat.rec (1 : ℚ) (fun _ ih ↦ p.1 * ih) p.2 : ℚ) :=
      Computable.nat_rec (f := fun p : ℚ × ℕ ↦ p.2) (g := fun _ ↦ (1 : ℚ))
        (h := fun p y ↦ p.1 * y.2) Computable.snd (Computable.const 1)
        (computable₂_ratMul.comp (Computable.fst.comp Computable.fst)
          (Computable.snd.comp Computable.snd))
    refine h.of_eq fun p ↦ ?_
    obtain ⟨r, n⟩ := p
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← ih]
  have hS : ComputableIn {charOracle B} fun d : ℕ × ℕ ↦ q (d, p₀) :=
    (hq.comp (Computable.id.pair (Computable.const p₀)).computableIn).of_eq fun _ ↦ rfl
  have hTq : Computable fun d : ℕ × ℕ ↦ (d.2 : ℚ) :=
    ComputableReals.computable_natCastRat.comp Computable.snd
  have hlo : ComputableIn {charOracle B} lo := by
    rw [hlo_def]
    exact computable₂_ratSub.computableIn₂.comp
      (computable₂_ratMul.comp (Computable.const (5 * ρ / 8)) hTq).computableIn hS
  have hhi : ComputableIn {charOracle B} hi := by
    rw [hhi_def]
    exact computable₂_ratSub.computableIn₂.comp
      (computable₂_ratMul.comp (Computable.const (7 * ρ / 8)) hTq).computableIn hS
  have hr : Computable fun dn : (ℕ × ℕ) × ℕ ↦ Denumerable.ofNat ℚ dn.2 :=
    (Computable.ofNat ℚ).comp Computable.snd
  have hlo' : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ lo dn.1 :=
    hlo.comp ComputableIn.fst
  have hhi' : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ hi dn.1 :=
    hhi.comp ComputableIn.fst
  have hA : Computable fun dn : (ℕ × ℕ) × ℕ ↦ decide (0 < Denumerable.ofNat ℚ dn.2) :=
    computable₂_ratLt.comp (Computable.const 0) hr
  have hpowlo : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      (Denumerable.ofNat ℚ dn.2) ^ (lo dn.1).den :=
    (hratpow.computableIn.comp
      (hr.computableIn.pair (computable_ratDen.computableIn.comp hlo'))).of_eq fun _ ↦ rfl
  have hpowhi : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      (Denumerable.ofNat ℚ dn.2) ^ (hi dn.1).den :=
    (hratpow.computableIn.comp
      (hr.computableIn.pair (computable_ratDen.computableIn.comp hhi'))).of_eq fun _ ↦ rfl
  have hzlo : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ (2 : ℚ) ^ (lo dn.1).num :=
    (hzpow.computableIn.comp (computable_ratNum.computableIn.comp hlo')).of_eq fun _ ↦ rfl
  have hzhi : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦ (2 : ℚ) ^ (hi dn.1).num :=
    (hzpow.computableIn.comp (computable_ratNum.computableIn.comp hhi')).of_eq fun _ ↦ rfl
  have hB : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      decide ((2 : ℚ) ^ (lo dn.1).num < (Denumerable.ofNat ℚ dn.2) ^ (lo dn.1).den) :=
    computable₂_ratLt.computableIn₂.comp hzlo hpowlo
  have hC : ComputableIn {charOracle B} fun dn : (ℕ × ℕ) × ℕ ↦
      decide ((Denumerable.ofNat ℚ dn.2) ^ (hi dn.1).den < (2 : ℚ) ^ (hi dn.1).num) :=
    computable₂_ratLt.computableIn₂.comp hpowhi hzhi
  have hand : Computable₂ fun a b : Bool ↦ (a && b) := (Primrec.dom_bool₂ _).to_comp
  obtain ⟨test, htest_def⟩ : ∃ test : (ℕ × ℕ) × ℕ → Bool, test = fun dn ↦
      decide (0 < Denumerable.ofNat ℚ dn.2 ∧
        (2 : ℚ) ^ (lo dn.1).num < (Denumerable.ofNat ℚ dn.2) ^ (lo dn.1).den ∧
        (Denumerable.ofNat ℚ dn.2) ^ (hi dn.1).den < (2 : ℚ) ^ (hi dn.1).num) := ⟨_, rfl⟩
  have htest : ComputableIn {charOracle B} test := by
    rw [htest_def]
    refine (hand.computableIn₂.comp hA.computableIn (hand.computableIn₂.comp hB hC)).of_eq
      fun dn ↦ ?_
    simp only [Bool.decide_and]
  -- the search and the total program
  have hsearch : PartrecIn {charOracle B} fun d : ℕ × ℕ ↦
      Nat.rfind fun n ↦ (Part.some (test (d, n)) : Part Bool) :=
    PartrecIn.rfind (p := fun d n ↦ (Part.some (test (d, n)) : Part Bool))
      (ComputableIn₂.mk (f := fun d n ↦ test (d, n)) htest).partrecIn₂
  have hc : ComputableIn {charOracle B} fun d : ℕ × ℕ ↦ decide (d.2 = 0) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.snd (Primrec.const 0))).to_comp.computableIn
  obtain ⟨Rpart, hRpart_def⟩ : ∃ Rpart : ℕ × ℕ →. ℚ, Rpart = fun d ↦
      bif decide (d.2 = 0) then Part.some (1 : ℚ) else
        (Nat.rfind fun n ↦ (Part.some (test (d, n)) : Part Bool)).map (Denumerable.ofNat ℚ) :=
    ⟨_, rfl⟩
  have hRpart : PartrecIn {charOracle B} Rpart := by
    rw [hRpart_def]
    exact PartrecIn.cond hc (ComputableIn.const (1 : ℚ)).partrecIn
      (hsearch.map ((Computable.ofNat ℚ).comp Computable.snd).computableIn)
  have hdom : ∀ d, (Rpart d).Dom := by
    intro d
    rw [hRpart_def]
    by_cases hT : d.2 = 0
    · simp [hT]
    · have hT' : (1 : ℝ) ≤ d.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
      have hlt : ((lo d : ℚ) : ℝ) < hi d := by
        rw [hlo_def, hhi_def]
        push_cast
        nlinarith
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (Real.rpow_lt_rpow_of_exponent_lt one_lt_two hlt)
      have hrpos : 0 < r := by exact_mod_cast (Real.rpow_pos_of_pos two_pos _).trans hr1
      obtain ⟨n, hn⟩ : ∃ n, Denumerable.ofNat ℚ n = r := ⟨_, Denumerable.ofNat_encode r⟩
      have ht : test (d, n) = true := by
        rw [htest_def]
        simp only [decide_eq_true_iff]
        rw [hn]
        exact ⟨hrpos, (hkey _ _ hrpos).mp hr1, (hkey' _ _ hrpos).mp hr2⟩
      simp only [hT, decide_false, Bool.cond_false, Part.map_Dom]
      exact Nat.rfind_dom.mpr ⟨n, Part.mem_some_iff.mpr ht.symm, fun _ ↦ trivial⟩
  refine ⟨ε, hε, fun d ↦ (Rpart d).get (hdom d),
    PartrecIn.of_eq_tot hRpart fun d ↦ Part.get_mem (hdom d), fun x T d hdT hdtol ↦ ?_⟩
  have hi' := d.mem_order hdT hdtol
  generalize d.idx = i at hi' ⊢
  have hS := hosc x T (OrbitDatum.ofMem hi') rfl le_rfl
  simp only [OrbitDatum.ofMem_idx] at hS
  have hq1 := hqerr (i, T) p₀
  dsimp only at hq1 ⊢
  by_cases hT : T = 0
  · subst hT
    have hR : (Rpart (i, 0)).get (hdom (i, 0)) = 1 := by
      simp [hRpart_def]
    rw [hR]
    simp [GeodesicReconstructionData.scaleMinus, birkhoffSum_zero_apply]
  · have hT' : (1 : ℝ) ≤ T := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
    have hmem0 : (Rpart (i, T)).get (hdom (i, T)) ∈ Rpart (i, T) := Part.get_mem _
    generalize (Rpart (i, T)).get (hdom (i, T)) = r at hmem0 ⊢
    have hmem := hmem0
    rw [hRpart_def] at hmem
    simp only [hT, decide_false, Bool.cond_false, Part.mem_map_iff] at hmem
    obtain ⟨n, hn, hrn⟩ := hmem
    have ht : test ((i, T), n) = true := (Part.mem_some_iff.mp (Nat.rfind_spec hn)).symm
    rw [htest_def] at ht
    simp only [decide_eq_true_iff] at ht
    rw [hrn] at ht
    obtain ⟨hrpos, hlo1, hhi1⟩ := ht
    have hab1 := abs_le.mp hS
    have hab2 := abs_lt.mp hq1
    have hρT : (ρ : ℝ) ≤ ρ * T := by nlinarith
    refine ⟨hrpos, ?_, ?_⟩
    · refine le_trans ?_ ((hkey _ _ hrpos).mpr hlo1).le
      unfold GeodesicReconstructionData.scaleMinus
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [hlo_def]
      push_cast
      linarith
    · refine ((hkey' _ _ hrpos).mpr hhi1).le.trans ?_
      unfold GeodesicReconstructionData.scaleMinus
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      rw [hhi_def]
      push_cast
      linarith

end OrbitDatum

end Kolmogorov.PointToSet
