/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.OrbitData
import KolmogorovMathlib.PointToSet.EffectiveLocalization.Search

/-!
# Effective localization from shadowing data (geodesic blueprint, Chapter D)

The node `geo:localization` of `geodesic_upper_bound_blueprint.md`
(OTL `Expansivity_algorithm`, refined in UEL "Effective reconstruction from finite orbit data
and a prescribed future"), together with the two topological facts its proof rests on.

Three forms are stated.

* `localization_core` (OTL form): a point `z` of a computably compact set `K`, uniquely
  determined inside `K` by shadowing data at all rational times, is a computable point.
* `localization_decoder` (UEL form, the one Chapter E consumes): one fixed `B`-partial
  recursive program takes a marked index `kp` (the past: `z₀` lies in the compact unstable
  plaque of `pIdx kp`), a Bowen-ball ideal index `i` and a duration `T` (the middle: `z₀`
  shadows the orbit of `ι i` at integer times `0,…,T`), a marked index `kq` (the future:
  `z₀` shadows the orbit of `pIdx kq` at integer times after `T`) and a precision `p`, and
  halts with an ideal index within `2⁻ᵖ` of `z₀`. Uniqueness of `z₀` comes from
  `plaque_expansivity` (Chapter B) through the Lipschitz constant on unit time intervals.
* `localization_decoder_proj`: the same, outputting the section point `(box j).proj z₀` of a
  flow box containing the plaque.

The mesh of the sample times is one, so no rational sample times are needed: the middle
orbit data are exactly an ideal point of `bowenBall f (T+1) x ε` (Chapter A), read at integer
times; downstream chapters package them as `OrbitDatum`s (`OrbitData.lean`), whose index is
the program input `i` here.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-! ### Topological ingredients -/

omit [CompactSpace X] in
/-- Cantor's intersection argument in the form used by the localization search: a decreasing
sequence of nonempty compact sets with singleton intersection `{z}` is eventually inside every
ball about `z`. Blueprint node `geo:localization`. -/
theorem exists_subset_ball_of_iInter_eq_singleton {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n))
    (hanti : Antitone K) {z : X} (hz : ⋂ n, K n = {z}) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n, K n ⊆ Metric.ball z δ := by
  by_contra hcon
  have hcon' : ∀ n, ¬ K n ⊆ Metric.ball z δ := fun n h ↦ hcon ⟨n, h⟩
  set t : ℕ → Set X := fun n ↦ K n \ Metric.ball z δ with ht
  have htd : ∀ i, t (i + 1) ⊆ t i := fun i ↦ Set.sdiff_subset_sdiff_left (hanti (Nat.le_succ i))
  have htn : ∀ i, (t i).Nonempty := fun i ↦ Set.not_subset.1 (hcon' i)
  have ht0 : IsCompact (t 0) := (hK 0).diff Metric.isOpen_ball
  have htcl : ∀ i, IsClosed (t i) := fun i ↦
    (hK i).isClosed.inter Metric.isOpen_ball.isClosed_compl
  obtain ⟨w, hw⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  have hwK : w ∈ ⋂ n, K n := Set.mem_iInter.2 fun n ↦ (Set.mem_iInter.1 hw n).1
  rw [hz, Set.mem_singleton_iff] at hwK
  exact (Set.mem_iInter.1 hw 0).2 (hwK ▸ Metric.mem_ball_self hδ)

/-- A bound on the orbit distance at every rational time extends to every real time, by
continuity of the flow. Blueprint node `geo:localization`. -/
theorem dist_flow_le_of_forall_rat (D : FlowData X) {w z : X} {c : ℝ}
    (h : ∀ q : ℚ, dist (D.φ (q : ℝ) w) (D.φ (q : ℝ) z) ≤ c) (t : ℝ) :
    dist (D.φ t w) (D.φ t z) ≤ c := by
  have hcont : Continuous fun t : ℝ ↦ dist (D.φ t w) (D.φ t z) :=
    (D.φ.continuous continuous_id continuous_const).dist
      (D.φ.continuous continuous_id continuous_const)
  have hclosed : IsClosed {t : ℝ | dist (D.φ t w) (D.φ t z) ≤ c} :=
    isClosed_le hcont continuous_const
  have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {t : ℝ | dist (D.φ t w) (D.φ t z) ≤ c} := by
    rintro _ ⟨q, rfl⟩
    exact h q
  have hall := hclosed.closure_subset_iff.2 hsub
  rw [Rat.denseRange_cast.closure_eq] at hall
  exact hall (Set.mem_univ t)

/-- A bound at the integer times `0,…,T` and at `T + n` for all `n`, together with the unit-time
Lipschitz constant `L`, bounds the forward orbit distance at every real `t ≥ 0` by `L` times
the sample bound (UEL, step "applying the flow for the remaining time after the preceding
sample"). Blueprint node `geo:localization`. -/
theorem dist_flow_le_of_integer_samples (D : FlowData X) {y z : X} {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, dist (D.φ (n : ℝ) y) (D.φ (n : ℝ) z) ≤ ρ) {t : ℝ} (ht : 0 ≤ t) :
    dist (D.φ t y) (D.φ t z) ≤ D.L * ρ := by
  set n := ⌊t⌋₊ with hn
  have h1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have h2 : t < n + 1 := Nat.lt_floor_add_one t
  have hs : |t - n| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have e : t - n + n = t := by ring
  have hy' : D.φ t y = D.φ (t - n) (D.φ (n : ℝ) y) := by rw [← Flow.map_add, e]
  have hz' : D.φ t z = D.φ (t - n) (D.φ (n : ℝ) z) := by rw [← Flow.map_add, e]
  rw [hy', hz']
  calc dist (D.φ (t - n) (D.φ (n : ℝ) y)) (D.φ (t - n) (D.φ (n : ℝ) z))
      ≤ D.L * dist (D.φ (n : ℝ) y) (D.φ (n : ℝ) z) := D.lipschitz_unit _ hs _ _
    _ ≤ D.L * ρ := mul_le_mul_of_nonneg_left (h n) (by linarith [D.one_le_L])

/-- Backward version of `dist_flow_le_of_integer_samples`: samples at the times `-n` bound the
backward orbit distance at every real `t ≥ 0`. Blueprint node `geo:localization` (reversed). -/
theorem dist_flow_le_of_integer_samples_backward (D : FlowData X) {y z : X} {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, dist (D.φ (-(n : ℝ)) y) (D.φ (-(n : ℝ)) z) ≤ ρ) {t : ℝ} (ht : 0 ≤ t) :
    dist (D.φ (-t) y) (D.φ (-t) z) ≤ D.L * ρ := by
  set n := ⌊t⌋₊ with hn
  have h1 : (n : ℝ) ≤ t := Nat.floor_le ht
  have h2 : t < n + 1 := Nat.lt_floor_add_one t
  have hs : |-(t - n)| ≤ 1 := by
    rw [abs_neg, abs_le]
    constructor <;> linarith
  have e : -(t - n) + -(n : ℝ) = -t := by ring
  have hy' : D.φ (-t) y = D.φ (-(t - n)) (D.φ (-(n : ℝ)) y) := by rw [← Flow.map_add, e]
  have hz' : D.φ (-t) z = D.φ (-(t - n)) (D.φ (-(n : ℝ)) z) := by rw [← Flow.map_add, e]
  rw [hy', hz']
  calc dist (D.φ (-(t - n)) (D.φ (-(n : ℝ)) y)) (D.φ (-(t - n)) (D.φ (-(n : ℝ)) z))
      ≤ D.L * dist (D.φ (-(n : ℝ)) y) (D.φ (-(n : ℝ)) z) := D.lipschitz_unit _ hs _ _
    _ ≤ D.L * ρ := mul_le_mul_of_nonneg_left (h n) (by linarith [D.one_le_L])

/-! ### The OTL form: shadowing data at all rational times -/

section core

variable (G : GeodesicReconstructionData X) (P : Presentation X) (A : Set ℕ)

/-- Effective localization, OTL form. Let `K` be computably compact with `z ∈ K`, let
`σ : ℚ → ℕ` be `A`-computable with `dist (ι (σ q)) (φ q z) ≤ r / 2` for every rational `q`,
and suppose `z` is the only point of `K` whose orbit stays within `3r/2` of the orbit of `z`
at every rational time. Then `z` is an `A`-computable point.
Blueprint node `geo:localization`. -/
theorem localization_core (hP : ComputablePresentationIn P A)
    (hflow : IsRepresentedFamilyIn P P A fun q : ℚ ↦ G.φ (q : ℝ)) {K : Set X}
    (hK : IsComputablyCompactIn P A K) {z : X} (hz : z ∈ K) {r : ℝ} (hr : 0 < r)
    {σ : ℚ → ℕ} (hσ : ComputableIn {charOracle A} σ)
    (hshadow : ∀ q : ℚ, dist (P.ι (σ q)) (G.φ (q : ℝ) z) ≤ r / 2)
    (huniq : ∀ w ∈ K, (∀ q : ℚ, dist (G.φ (q : ℝ) w) (G.φ (q : ℝ) z) ≤ 3 * r / 2) → w = z) :
    IsComputablePointIn P A z := by
  -- a rational tolerance strictly between `r / 2` and `r`
  obtain ⟨ρ, hρ1, hρ2⟩ := exists_rat_btwn (show r / 2 < r by linarith)
  -- violation sets at the rational times, enumerated through `Denumerable.ofNat`
  have hσ' : ComputableIn {charOracle A} fun m : ℕ ↦ σ (Denumerable.ofNat ℚ m) :=
    hσ.comp (Computable.ofNat ℚ).computableIn
  have hS : IsCeOpenFamilyIn P A fun d : ℕ × ℚ ↦
      {w | (d.2 : ℝ) < dist w (P.ι (σ (Denumerable.ofNat ℚ d.1)))} :=
    isCeOpenFamilyIn_lt_dist hP (w₀ := fun m ↦ P.ι (σ (Denumerable.ofNat ℚ m)))
      (a := fun m _ ↦ σ (Denumerable.ofNat ℚ m)) (fun m ↦ isCauchyName_const P _)
      (hσ'.comp ComputableIn.fst)
  have hV := hflow.preimage_ceOpen hS
  have hg : Computable fun nm : ℕ × ℕ ↦ (Denumerable.ofNat ℚ nm.2, (nm.2, ρ)) :=
    ((Computable.ofNat ℚ).comp Computable.snd).pair (Computable.snd.pair (Computable.const ρ))
  have hp : Computable fun nm : ℕ × ℕ ↦ decide (nm.2 < nm.1) :=
    (Primrec.nat_lt.comp Primrec.snd Primrec.fst).decide.to_comp
  let V : ℕ → Set X := fun m ↦ G.φ ((Denumerable.ofNat ℚ m : ℚ) : ℝ) ⁻¹'
    {w | (ρ : ℝ) < dist w (P.ι (σ (Denumerable.ofNat ℚ m)))}
  let W : ℕ → Set X := fun n ↦ ⋃ m, if m < n then V m else ∅
  have hW : IsCeOpenFamilyIn P A W :=
    ((hV.comp hg).ite (p := fun nm : ℕ × ℕ ↦ nm.2 < nm.1) hp).iUnion
  let U : (ℕ × ℕ) × ℕ → Set X := fun w ↦
    W w.2 ∪ Metric.ball (P.ι w.1.2) (((2 ^ w.1.1 : ℚ)⁻¹ : ℚ) : ℝ)
  have hbidx : Computable fun w : (ℕ × ℕ) × ℕ ↦ (w.1.2, (2 ^ w.1.1 : ℚ)⁻¹) :=
    (Computable.snd.comp Computable.fst).pair
      (computable_rat_inv_two_pow.comp (Computable.fst.comp Computable.fst))
  have hU : IsCeOpenFamilyIn P A U :=
    (hW.comp (Computable.snd : Computable fun w : (ℕ × ℕ) × ℕ ↦ w.2)).union
      ((isCeOpenFamilyIn_ball P A hP).comp hbidx)
  have hcert := (IsComputablyCompactIn.subset_ceOpen_isREIn P A hK hU).exists
  -- `z` violates no constraint
  have hzW : ∀ n, z ∉ W n := by
    intro n hz
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
    rw [Set.mem_ite_empty_right] at hm
    have hlt : (ρ : ℝ) < dist (G.φ ((Denumerable.ofNat ℚ m : ℚ) : ℝ) z)
        (P.ι (σ (Denumerable.ofNat ℚ m))) := hm.2
    have hle := hshadow (Denumerable.ofNat ℚ m)
    rw [dist_comm] at hle
    linarith
  -- totality of the certified search: a finite subcover of `K` minus the target ball
  have htot : ∀ p : ℕ, ∃ c : ℕ, ∃ n, K ⊆ U ((p, c), n) := by
    intro p
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp P.dense z (dyadicRadius p) (dyadicRadius_pos p)
    have hzball : z ∈ Metric.ball (P.ι c) (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := by
      rw [cast_inv_two_pow_eq_dyadicRadius]
      exact hc
    have hVopen : ∀ m, IsOpen (V m) := fun m ↦
      (isOpen_lt continuous_const (continuous_id.dist continuous_const)).preimage
        (G.φ.continuous_toFun _)
    have hcov : K \ Metric.ball (P.ι c) (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) ⊆ ⋃ m, V m := by
      intro w hw
      have hwz : w ≠ z := fun h ↦ hw.2 (h ▸ hzball)
      have hw' : ¬ ∀ q : ℚ, dist (G.φ (q : ℝ) w) (G.φ (q : ℝ) z) ≤ 3 * r / 2 :=
        fun h ↦ hwz (huniq w hw.1 h)
      obtain ⟨q, hq⟩ := not_forall.mp hw'
      have hq' := not_le.mp hq
      obtain ⟨m, rfl⟩ : ∃ m, Denumerable.ofNat ℚ m = q := ⟨_, Denumerable.ofNat_encode q⟩
      refine Set.mem_iUnion.mpr ⟨m, ?_⟩
      change (ρ : ℝ) < dist (G.φ ((Denumerable.ofNat ℚ m : ℚ) : ℝ) w)
        (P.ι (σ (Denumerable.ofNat ℚ m)))
      have hsh := hshadow (Denumerable.ofNat ℚ m)
      have htri := dist_triangle (G.φ ((Denumerable.ofNat ℚ m : ℚ) : ℝ) w)
        (P.ι (σ (Denumerable.ofNat ℚ m))) (G.φ ((Denumerable.ofNat ℚ m : ℚ) : ℝ) z)
      linarith
    obtain ⟨t, ht⟩ := (hK.1.diff Metric.isOpen_ball).elim_finite_subcover V hVopen hcov
    refine ⟨c, t.sup id + 1, fun w hw ↦ ?_⟩
    by_cases hwb : w ∈ Metric.ball (P.ι c) (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ)
    · exact Or.inr hwb
    · obtain ⟨m, hm, hwm⟩ := Set.mem_iUnion₂.mp (ht ⟨hw, hwb⟩)
      refine Or.inl (Set.mem_iUnion.mpr ⟨m, ?_⟩)
      rw [Set.mem_ite_empty_right]
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hm), hwm⟩
  obtain ⟨g, hg, hgood⟩ := hcert.exists_computableIn_choice htot
  refine ⟨g, fun p ↦ ?_, hg⟩
  obtain ⟨n, hn⟩ := hgood p
  rcases hn hz with h | h
  · exact (hzW n h).elim
  · have h' : dist z (P.ι (g p)) < (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := h
    rw [cast_inv_two_pow_eq_dyadicRadius] at h'
    rw [dist_comm]
    exact h'

/-- The uniqueness hypothesis of `localization_core` follows from expansivity on the regular
set (G9) when `K` meets the short orbit segment of `z` only at `z`: with `3r/2 ≤ 2 rExp`, a
point of `K` whose orbit stays `3r/2`-close at all rational times is a time shift `φ s z`,
`|s| ≤ 2 rExp`, hence equals `z`. Blueprint node `geo:localization`. -/
theorem localization_uniq_of_expansive {K : Set X} {z : X} (hz : z ∈ G.Reg) {r : ℝ}
    (hr : 3 * r / 2 ≤ 2 * G.rExp)
    (hK : ∀ s : ℝ, |s| ≤ 2 * G.rExp → G.φ s z ∈ K → G.φ s z = z) :
    ∀ w ∈ K, (∀ q : ℚ, dist (G.φ (q : ℝ) w) (G.φ (q : ℝ) z) ≤ 3 * r / 2) → w = z := by
  intro w hwK hw
  have hall : ∀ t : ℝ, dist (G.φ t w) (G.φ t z) ≤ 2 * G.rExp := fun t ↦
    (dist_flow_le_of_forall_rat G.toFlowData hw t).trans hr
  obtain ⟨s, hs, hws⟩ := G.expansive z hz w hall
  rw [hws]
  exact hK s hs (hws ▸ hwK)

end core

/-! ### Shrinkable plaques -/

namespace GeodesicReconstructionData

variable (G : GeodesicReconstructionData X)

/-- A compact unstable plaque of radius `r ≤ ε₀` lies in the closure of the `ε₀`-plaque
(blueprint item 8.1). -/
theorem Kplaque_subset_closure_plaque {p : X} {r : ℚ} (hr : 0 < r)
    {ε₀ : ℝ} (hrε : (r : ℝ) ≤ ε₀) : G.Kplaque r p ⊆ closure (G.plaque .u ε₀ p) :=
  (G.Kplaque_spec p r hr).2.2.trans
    (closure_mono fun _ hy ↦ ⟨hy.1, lt_of_lt_of_le hy.2 hrε⟩)

/-- Stable counterpart of `Kplaque_subset_closure_plaque`. -/
theorem Kplaque'_subset_closure_plaque {p : X} {r : ℚ} (hr : 0 < r)
    {ε₀ : ℝ} (hrε : (r : ℝ) ≤ ε₀) : G.Kplaque' r p ⊆ closure (G.plaque .s ε₀ p) :=
  (G.Kplaque'_spec p r hr).2.2.trans
    (closure_mono fun _ hy ↦ ⟨hy.1, lt_of_lt_of_le hy.2 hrε⟩)

end GeodesicReconstructionData

/-! ### The UEL form: finite orbit data with a marked past and a marked future -/

namespace EffectiveGeodesicData

variable {G : GeodesicReconstructionData X} {P : Presentation X} {B : Set ℕ}
  (E : EffectiveGeodesicData G P B)
include E

/-- The constraint set of the decoder: points of the compact unstable plaque of radius `r` of
the marked point `pIdx kp` that shadow the orbit of the ideal point `ι i` at integer times
`0,…,T` and the orbit of the marked point `pIdx kq` at integer times after `T`, both within
`ρ`. Blueprint node `geo:localization`. -/
def shadowSet (ρ : ℝ) (r : ℚ) (kp i T kq : ℕ) : Set X :=
  {z ∈ G.Kplaque r (E.pIdx kp) |
    (∀ j : ℕ, j ≤ T → dist (G.φ (j : ℝ) z) (G.φ (j : ℝ) (P.ι i)) ≤ ρ) ∧
    ∀ n : ℕ, dist (G.φ ((T : ℝ) + n) z) (G.φ (n : ℝ) (E.pIdx kq)) ≤ ρ}

/-- Two points of the constraint set have forward orbits within `2 L ρ` for all real `t ≥ 0`.
Blueprint node `geo:localization`. -/
theorem dist_flow_le_of_mem_shadowSet {ρ : ℝ} (hρ : 0 ≤ ρ) {r : ℚ} {kp i T kq : ℕ} {y z : X}
    (hy : y ∈ E.shadowSet ρ r kp i T kq) (hz : z ∈ E.shadowSet ρ r kp i T kq) {t : ℝ}
    (ht : 0 ≤ t) : dist (G.φ t y) (G.φ t z) ≤ 2 * G.L * ρ := by
  obtain ⟨_, hy1, hy2⟩ := hy
  obtain ⟨_, hz1, hz2⟩ := hz
  have hint : ∀ n : ℕ, dist (G.φ (n : ℝ) y) (G.φ (n : ℝ) z) ≤ 2 * ρ := by
    intro n
    rcases le_or_gt n T with hn | hn
    · calc dist (G.φ (n : ℝ) y) (G.φ (n : ℝ) z)
          ≤ dist (G.φ (n : ℝ) y) (G.φ (n : ℝ) (P.ι i)) +
              dist (G.φ (n : ℝ) (P.ι i)) (G.φ (n : ℝ) z) := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add (hy1 n hn) (by rw [dist_comm]; exact hz1 n hn)
        _ = 2 * ρ := by ring
    · obtain ⟨m, rfl⟩ : ∃ m, n = T + m := ⟨n - T, by omega⟩
      have e : ((T + m : ℕ) : ℝ) = (T : ℝ) + m := by push_cast; ring
      rw [e]
      calc dist (G.φ ((T : ℝ) + m) y) (G.φ ((T : ℝ) + m) z)
          ≤ dist (G.φ ((T : ℝ) + m) y) (G.φ (m : ℝ) (E.pIdx kq)) +
              dist (G.φ (m : ℝ) (E.pIdx kq)) (G.φ ((T : ℝ) + m) z) := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add (hy2 m) (by rw [dist_comm]; exact hz2 m)
        _ = 2 * ρ := by ring
  have hL := dist_flow_le_of_integer_samples G.toFlowData (by linarith) hint ht
  calc dist (G.φ t y) (G.φ t z) ≤ G.L * (2 * ρ) := hL
    _ = 2 * G.L * ρ := by ring

/-- Uniqueness in the constraint set: over a compact regular set `Q` of base points, with
`a, ε₀` from `plaque_expansivity`, a tolerance `ρ` with `2 L ρ < a`, and a plaque radius
`0 < r ≤ ε₀`, the constraint set has at most one point.
Blueprint node `geo:localization` (UEL "Then `z₀` is unique"). -/
theorem shadowSet_subsingleton {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℝ, 0 ≤ ρ → 2 * G.L * ρ < a →
      ∀ (kp : ℕ) (r : ℚ) (i T kq : ℕ), E.pIdx kp ∈ Q → 0 < r ∧ (r : ℝ) ≤ ε₀ →
        (E.shadowSet ρ r kp i T kq).Subsingleton := by
  obtain ⟨a, ha, ε₀, hε₀, hexp⟩ := G.plaque_expansivity hQ hQR
  refine ⟨a, ha, ε₀, hε₀, fun ρ hρ hρa kp r i T kq hkp ⟨hr, hrε⟩ y hy z hz ↦ ?_⟩
  obtain ⟨_, huniq⟩ := hexp (E.pIdx kp) hkp
  have hK := G.Kplaque_subset_closure_plaque (p := E.pIdx kp) hr hrε
  exact huniq y (hK hy.1) z (hK hz.1) fun t ht ↦
    (E.dist_flow_le_of_mem_shadowSet hρ hy hz ht).trans hρa.le

/-- The complement of the constraint set inside the plaque is c.e. open uniformly in the data:
violations of the closed constraints are strict inequalities on computable reals (the orbit
of `ι i` at integer times, the orbit of `pIdx kq`, and the point itself). The radius
is part of the index but does not enter the violation set. Blueprint node `geo:localization`. -/
theorem shadowSet_compl_ceOpen (ρ : ℚ) :
    ∃ O : ℕ × ℚ × ℕ × ℕ × ℕ → Set X, IsCeOpenFamilyIn P B O ∧
      ∀ (kp : ℕ) (r : ℚ) (i T kq : ℕ),
        G.Kplaque r (E.pIdx kp) \ E.shadowSet ρ r kp i T kq =
          G.Kplaque r (E.pIdx kp) ∩ O (kp, r, i, T, kq) := by
  -- names of the reference orbits, uniformly in the time and the index
  obtain ⟨b₁, hb₁c, hb₁⟩ := IsRepresentedFamilyIn.names_uniform E.presentation
    E.flow_represented (x := P.ι) (a := fun i _ ↦ i) (fun i ↦ isCauchyName_const P i)
    ComputableIn.fst
  obtain ⟨aP, haPc, haP⟩ := E.pIdx_names
  obtain ⟨b₂, hb₂c, hb₂⟩ :=
    IsRepresentedFamilyIn.names_uniform E.presentation E.flow_represented haP haPc
  -- the sets `{w | ρ < dist w w₀}` about the reference points, as c.e. open families
  have hS₁ : IsCeOpenFamilyIn P B fun d : (ℚ × ℕ) × ℚ ↦
      {w | (d.2 : ℝ) < dist w (G.φ (d.1.1 : ℝ) (P.ι d.1.2))} :=
    isCeOpenFamilyIn_lt_dist E.presentation (w₀ := fun qi : ℚ × ℕ ↦ G.φ (qi.1 : ℝ) (P.ι qi.2))
      (a := fun qi ↦ b₁ qi.1 qi.2) (fun qi ↦ hb₁ qi.1 qi.2) hb₁c
  have hS₂ : IsCeOpenFamilyIn P B fun d : (ℚ × ℕ) × ℚ ↦
      {w | (d.2 : ℝ) < dist w (G.φ (d.1.1 : ℝ) (E.pIdx d.1.2))} :=
    isCeOpenFamilyIn_lt_dist E.presentation
      (w₀ := fun qk : ℚ × ℕ ↦ G.φ (qk.1 : ℝ) (E.pIdx qk.2))
      (a := fun qk ↦ b₂ qk.1 qk.2) (fun qk ↦ hb₂ qk.1 qk.2) hb₂c
  -- pulled back by the flow at the sample times and restricted to the sample range
  have hA := E.flow_represented.preimage_ceOpen hS₁
  have hB := E.flow_represented.preimage_ceOpen hS₂
  have pi : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have pT : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have pkq : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have hg₁ : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦
      (((w.2 : ℕ) : ℚ), (((w.2 : ℕ) : ℚ), w.1.2.2.1), ρ) :=
    (ComputableReals.computable_natCastRat.comp Computable.snd).pair
      (((ComputableReals.computable_natCastRat.comp Computable.snd).pair pi).pair
        (Computable.const ρ))
  have hp : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ decide (w.2 ≤ w.1.2.2.2.1) :=
    (Primrec.nat_le.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))))).decide.to_comp
  have hO₁ := ((hA.comp hg₁).ite
    (p := fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.2 ≤ w.1.2.2.2.1) hp).iUnion
  have hg₂ : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦
      (((w.1.2.2.2.1 + w.2 : ℕ) : ℚ), (((w.2 : ℕ) : ℚ), w.1.2.2.2.2), ρ) :=
    (ComputableReals.computable_natCastRat.comp (Primrec.nat_add.to_comp.comp pT
      Computable.snd)).pair
      (((ComputableReals.computable_natCastRat.comp Computable.snd).pair pkq).pair
        (Computable.const ρ))
  have hO₂ := (hB.comp hg₂).iUnion
  refine ⟨_, hO₁.union hO₂, fun kp r i T kq ↦ ?_⟩
  ext z
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion,
    Set.mem_ite_empty_right, Set.mem_preimage, Set.mem_ofPred_eq, Rat.cast_natCast,
    Nat.cast_add, Rat.cast_add, shadowSet]
  constructor
  · rintro ⟨hzK, hzS⟩
    refine ⟨hzK, ?_⟩
    by_contra hO
    simp only [not_or, not_exists, not_and, not_lt] at hO
    exact hzS ⟨hzK, hO.1, hO.2⟩
  · rintro ⟨hzK, hO⟩
    refine ⟨hzK, fun hzS ↦ ?_⟩
    rcases hO with ⟨j, hj, hlt⟩ | ⟨n, hlt⟩
    · exact absurd (hzS.2.1 j hj) (not_le.mpr hlt)
    · exact absurd (hzS.2.2 n) (not_le.mpr hlt)

/-- The constraint sets lie in the (computably compact) plaque family of `Kplaque_cc`. -/
theorem shadowSet_subset_family (ρ : ℝ) (kp : ℕ) (r : ℚ) (i T kq : ℕ) (hr : 0 < r) :
    E.shadowSet ρ r kp i T kq ⊆
      (fun kr : ℕ × ℚ ↦ if 0 < kr.2 then G.Kplaque kr.2 (E.pIdx kr.1) else ∅) (kp, r) := by
  intro z hz
  change z ∈ (if 0 < r then G.Kplaque r (E.pIdx kp) else ∅)
  rw [ite_eq_left hr]
  exact hz.1

/-- The certified search on the forward constraint sets: one `B`-partial recursive program
`loc` which, on input `(kp, r, i, T, kq, p)` with `0 < r` and the constraint set a
subsingleton, halts with an ideal index within `2⁻ᵖ` of every point of the constraint set.
This is `certified_localization` for the plaque family of `Kplaque_cc`, reindexed by the full
data, and the violation sets of `shadowSet_compl_ceOpen`. Blueprint node `geo:localization`. -/
theorem shadowSet_decoder (ρ : ℚ) :
    ∃ loc : ℕ × ℚ × ℕ × ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} loc ∧
      ∀ (kp : ℕ) (r : ℚ) (i T kq p : ℕ), 0 < r → (E.shadowSet ρ r kp i T kq).Subsingleton →
        ∀ z₀ ∈ E.shadowSet ρ r kp i T kq, (loc (kp, r, i, T, kq, p)).Dom ∧
          ∀ q ∈ loc (kp, r, i, T, kq, p), dist (P.ι q) z₀ < dyadicRadius p := by
  obtain ⟨O, hO, hOeq⟩ := E.shadowSet_compl_ceOpen ρ
  -- the plaque family reindexed by the full data (no type ascription: the stated `ite` form
  -- makes the later unifications slow)
  have hK := E.Kplaque_cc.comp (κ := ℕ × ℚ × ℕ × ℕ × ℕ)
    (Computable.fst.pair (Computable.fst.comp Computable.snd))
  obtain ⟨loc, hloc, hspec⟩ := certified_localization hK hO E.presentation
  -- regroup the input `(kp, r, i, T, kq, p)` as `((kp, r, i, T, kq), p)`
  have hre : Computable fun w : ℕ × ℚ × ℕ × ℕ × ℕ × ℕ ↦
      ((w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1), w.2.2.2.2.2) :=
    (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.snd)))))))).pair
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp Computable.snd))))
  refine ⟨fun w ↦ loc ((w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1), w.2.2.2.2.2),
    hloc.comp hre.computableIn, fun kp r i T kq p hr hss z₀ hz₀ ↦ ?_⟩
  refine hspec (kp, r, i, T, kq) p _ (E.shadowSet_subset_family ρ kp r i T kq hr) ?_ hss z₀ hz₀
  change (if 0 < r then G.Kplaque r (E.pIdx kp) else ∅) \ _ =
    (if 0 < r then G.Kplaque r (E.pIdx kp) else ∅) ∩ _
  rw [ite_eq_left hr]
  exact hOeq kp r i T kq

/-- Effective localization, UEL form: the uniform decoder. For a compact regular `Q` there are
`a, ε₀ > 0` such that for every rational tolerance `ρ` with `2 L ρ < a` there is one
`B`-partial recursive program `loc` which, on input `(kp, r, i, T, kq, p)` with `pIdx kp ∈ Q`,
a plaque radius `0 < r ≤ ε₀` and the constraint set nonempty, halts with an ideal index
within `2⁻ᵖ` of the unique constrained point. The program uses neither a computable
separation-time bound nor computable holonomy maps: it dovetails, over ideal centers `c`,
the semidecidable test "plaque ⊆ (violation set) ∪ ball(c, 2⁻ᵖ)".
Blueprint node `geo:localization`. -/
theorem localization_decoder {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℚ, 0 < ρ → 2 * G.L * ρ < a →
      ∃ loc : ℕ × ℚ × ℕ × ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} loc ∧
        ∀ (kp : ℕ) (r : ℚ) (i T kq p : ℕ), E.pIdx kp ∈ Q → 0 < r ∧ (r : ℝ) ≤ ε₀ →
          ∀ z₀ ∈ E.shadowSet ρ r kp i T kq,
            (loc (kp, r, i, T, kq, p)).Dom ∧
              ∀ q ∈ loc (kp, r, i, T, kq, p), dist (P.ι q) z₀ < dyadicRadius p := by
  obtain ⟨a, ha, ε₀, hε₀, hsub⟩ := E.shadowSet_subsingleton hQ hQR
  refine ⟨a, ha, ε₀, hε₀, fun ρ hρ hρa ↦ ?_⟩
  obtain ⟨loc, hloc, hspec⟩ := E.shadowSet_decoder ρ
  exact ⟨loc, hloc, fun kp r i T kq p hkp hr z₀ hz₀ ↦
    hspec kp r i T kq p hr.1 (hsub ρ (by exact_mod_cast hρ.le) hρa kp r i T kq hkp hr) z₀ hz₀⟩

/-- Flow-box variant: if the plaque lies in the domain of the box `j`, the same search
computes the section point `(box j).proj z₀` (replace the target ball by its preimage under
the represented projection). Blueprint node `geo:localization` ("Alternatively, in a
prescribed computable flow box…"). -/
theorem localization_decoder_proj {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℚ, 0 < ρ → 2 * G.L * ρ < a →
      ∃ loc : Fin G.nBoxes × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} loc ∧
        ∀ (j : Fin G.nBoxes) (kp : ℕ) (r : ℚ) (i T kq p : ℕ), E.pIdx kp ∈ Q →
          0 < r ∧ (r : ℝ) ≤ ε₀ → G.Kplaque r (E.pIdx kp) ⊆ (G.box j).U →
          ∀ z₀ ∈ E.shadowSet ρ r kp i T kq,
            (loc (j, kp, r, i, T, kq, p)).Dom ∧
              ∀ q ∈ loc (j, kp, r, i, T, kq, p),
                dist (P.ι q) ((G.box j).proj z₀) < dyadicRadius p := by
  obtain ⟨a, ha, ε₀, hε₀, hsub⟩ := E.shadowSet_subsingleton hQ hQR
  refine ⟨a, ha, ε₀, hε₀, fun ρ hρ hρa ↦ ?_⟩
  obtain ⟨O, hO, hOeq⟩ := E.shadowSet_compl_ceOpen ρ
  -- the represented-on relations of the projections, uniformly in the box
  have hbox : ∀ j, ∃ R : (ℕ × ℚ) × (ℕ × ℚ) → Prop, IsREIn B R ∧
      (∀ b c, R (b, c) → 0 < b.2 ∧ 0 < c.2 ∧
        (G.box j).proj '' (basicBall P b ∩ (G.box j).U) ⊆ basicBall P c) ∧
      ∀ x ∈ (G.box j).U, ∀ c, (G.box j).proj x ∈ basicBall P c →
        ∃ b, R (b, c) ∧ x ∈ basicBall P b := fun j ↦ E.box_proj j
  choose R hRre hRs hRc using hbox
  -- the search index is `(j, kp, r, i, T, kq)`: the plaque family, the violation sets and the
  -- projection relations reindexed by it
  have hK := E.Kplaque_cc.comp (κ := Fin G.nBoxes × ℕ × ℚ × ℕ × ℕ × ℕ)
    ((Computable.fst.comp Computable.snd).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hO' : IsCeOpenFamilyIn P B fun k : Fin G.nBoxes × ℕ × ℚ × ℕ × ℕ × ℕ ↦ O k.2 :=
    hO.comp Computable.snd
  have hRu : IsREIn B fun w : (Fin G.nBoxes × ℕ × ℚ × ℕ × ℕ × ℕ) × ((ℕ × ℚ) × (ℕ × ℚ)) ↦
      R w.1.1 w.2 :=
    (isREIn_fin_uniform hRre).comp
      ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
  obtain ⟨loc, hloc, hspec⟩ := certified_localization_map hK hO' E.presentation
    (D := fun k ↦ (G.box k.1).U) (f := fun k ↦ (G.box k.1).proj) hRu
    (fun k b c h ↦ hRs k.1 b c h) (fun k x hx c hc ↦ hRc k.1 x hx c hc)
  -- regroup the input `(j, kp, r, i, T, kq, p)` as `((j, kp, r, i, T, kq), p)`
  have hre : Computable fun w : Fin G.nBoxes × ℕ × ℚ × ℕ × ℕ × ℕ × ℕ ↦
      ((w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1), w.2.2.2.2.2.2) :=
    (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
          ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.snd)))).pair
            (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
              (Computable.snd.comp (Computable.snd.comp Computable.snd)))))))))).pair
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
  refine ⟨fun w ↦ loc ((w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1),
    w.2.2.2.2.2.2), hloc.comp hre.computableIn, fun j kp r i T kq p hkp hr hKU z₀ hz₀ ↦ ?_⟩
  have hss := hsub ρ (by exact_mod_cast hρ.le) hρa kp r i T kq hkp hr
  refine hspec (j, kp, r, i, T, kq) p _ (E.shadowSet_subset_family ρ kp r i T kq hr.1) ?_ hss
    ?_ z₀ hz₀
  · change (if 0 < r then G.Kplaque r (E.pIdx kp) else ∅) \ _ =
      (if 0 < r then G.Kplaque r (E.pIdx kp) else ∅) ∩ _
    rw [ite_eq_left hr.1]
    exact hOeq kp r i T kq
  · change (if 0 < r then G.Kplaque r (E.pIdx kp) else ∅) ⊆ (G.box j).U
    rw [ite_eq_left hr.1]
    exact hKU

/-- The decoder's output is a computable function of its inputs on the valid domain, so a
point located by it from `B`-computable data is a `B`-computable point.
Blueprint node `geo:localization`. -/
theorem isComputablePointIn_of_shadowSet {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℚ, 0 < ρ → 2 * G.L * ρ < a →
      ∀ (kp : ℕ) (r : ℚ) (i T kq : ℕ), E.pIdx kp ∈ Q → 0 < r ∧ (r : ℝ) ≤ ε₀ →
        ∀ z₀ ∈ E.shadowSet ρ r kp i T kq, IsComputablePointIn P B z₀ := by
  obtain ⟨a, ha, ε₀, hε₀, hdec⟩ := E.localization_decoder hQ hQR
  refine ⟨a, ha, ε₀, hε₀, fun ρ hρ hρa kp r i T kq hkp hr z₀ hz₀ ↦ ?_⟩
  obtain ⟨loc, hloc, hspec⟩ := hdec ρ hρ hρa
  have hin : Computable fun p : ℕ ↦ (kp, r, i, T, kq, p) :=
    (Computable.const kp).pair ((Computable.const r).pair ((Computable.const i).pair
      ((Computable.const T).pair ((Computable.const kq).pair Computable.id))))
  exact certified_localization_point hloc hin fun p ↦ hspec kp r i T kq p hkp hr z₀ hz₀

/-! ### Stable (time-reversed) version, for the backward bracket -/

/-- The time-reversed constraint set: points of the compact stable plaque of radius `r` of
`pIdx kp` shadowing the backward orbit of `ι i` at times `0,…,T` and the backward orbit of
`pIdx kq` after `T`. Blueprint node `geo:localization` (reversed). -/
def shadowSetBackward (ρ : ℝ) (r : ℚ) (kp i T kq : ℕ) : Set X :=
  {z ∈ G.Kplaque' r (E.pIdx kp) |
    (∀ j : ℕ, j ≤ T → dist (G.φ (-(j : ℝ)) z) (G.φ (-(j : ℝ)) (P.ι i)) ≤ ρ) ∧
    ∀ n : ℕ, dist (G.φ (-((T : ℝ) + n)) z) (G.φ (-(n : ℝ)) (E.pIdx kq)) ≤ ρ}

/-- Two points of the reversed constraint set have backward orbits within `2 L ρ` for all real
`t ≥ 0`. Blueprint node `geo:localization` (reversed). -/
theorem dist_flow_le_of_mem_shadowSetBackward {ρ : ℝ} (hρ : 0 ≤ ρ) {r : ℚ} {kp i T kq : ℕ}
    {y z : X} (hy : y ∈ E.shadowSetBackward ρ r kp i T kq)
    (hz : z ∈ E.shadowSetBackward ρ r kp i T kq) {t : ℝ} (ht : 0 ≤ t) :
    dist (G.φ (-t) y) (G.φ (-t) z) ≤ 2 * G.L * ρ := by
  obtain ⟨_, hy1, hy2⟩ := hy
  obtain ⟨_, hz1, hz2⟩ := hz
  have hint : ∀ n : ℕ, dist (G.φ (-(n : ℝ)) y) (G.φ (-(n : ℝ)) z) ≤ 2 * ρ := by
    intro n
    rcases le_or_gt n T with hn | hn
    · calc dist (G.φ (-(n : ℝ)) y) (G.φ (-(n : ℝ)) z)
          ≤ dist (G.φ (-(n : ℝ)) y) (G.φ (-(n : ℝ)) (P.ι i)) +
              dist (G.φ (-(n : ℝ)) (P.ι i)) (G.φ (-(n : ℝ)) z) := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add (hy1 n hn) (by rw [dist_comm]; exact hz1 n hn)
        _ = 2 * ρ := by ring
    · obtain ⟨m, rfl⟩ : ∃ m, n = T + m := ⟨n - T, by omega⟩
      have e : -((T + m : ℕ) : ℝ) = -((T : ℝ) + m) := by push_cast; ring
      rw [e]
      calc dist (G.φ (-((T : ℝ) + m)) y) (G.φ (-((T : ℝ) + m)) z)
          ≤ dist (G.φ (-((T : ℝ) + m)) y) (G.φ (-(m : ℝ)) (E.pIdx kq)) +
              dist (G.φ (-(m : ℝ)) (E.pIdx kq)) (G.φ (-((T : ℝ) + m)) z) := dist_triangle _ _ _
        _ ≤ ρ + ρ := add_le_add (hy2 m) (by rw [dist_comm]; exact hz2 m)
        _ = 2 * ρ := by ring
  have hL := dist_flow_le_of_integer_samples_backward G.toFlowData (by linarith) hint ht
  calc dist (G.φ (-t) y) (G.φ (-t) z) ≤ G.L * (2 * ρ) := hL
    _ = 2 * G.L * ρ := by ring

/-- Uniqueness in the reversed constraint set, from backward plaque expansivity.
Blueprint node `geo:localization` (reversed). -/
theorem shadowSetBackward_subsingleton {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℝ, 0 ≤ ρ → 2 * G.L * ρ < a →
      ∀ (kp : ℕ) (r : ℚ) (i T kq : ℕ), E.pIdx kp ∈ Q → 0 < r ∧ (r : ℝ) ≤ ε₀ →
        (E.shadowSetBackward ρ r kp i T kq).Subsingleton := by
  obtain ⟨a, ha, ε₀, hε₀, hexp⟩ := G.plaque_expansivity_backward hQ hQR
  refine ⟨a, ha, ε₀, hε₀, fun ρ hρ hρa kp r i T kq hkp ⟨hr, hrε⟩ y hy z hz ↦ ?_⟩
  obtain ⟨_, huniq⟩ := hexp (E.pIdx kp) hkp
  have hK := G.Kplaque'_subset_closure_plaque (p := E.pIdx kp) hr hrε
  exact huniq y (hK hy.1) z (hK hz.1) fun t ht ↦
    (E.dist_flow_le_of_mem_shadowSetBackward hρ hy hz ht).trans hρa.le

/-- The complement of the reversed constraint set inside the stable plaque is c.e. open
uniformly in the data. Blueprint node `geo:localization` (reversed). -/
theorem shadowSetBackward_compl_ceOpen (ρ : ℚ) :
    ∃ O : ℕ × ℚ × ℕ × ℕ × ℕ → Set X, IsCeOpenFamilyIn P B O ∧
      ∀ (kp : ℕ) (r : ℚ) (i T kq : ℕ),
        G.Kplaque' r (E.pIdx kp) \ E.shadowSetBackward ρ r kp i T kq =
          G.Kplaque' r (E.pIdx kp) ∩ O (kp, r, i, T, kq) := by
  obtain ⟨b₁, hb₁c, hb₁⟩ := IsRepresentedFamilyIn.names_uniform E.presentation
    E.flow_represented (x := P.ι) (a := fun i _ ↦ i) (fun i ↦ isCauchyName_const P i)
    ComputableIn.fst
  obtain ⟨aP, haPc, haP⟩ := E.pIdx_names
  obtain ⟨b₂, hb₂c, hb₂⟩ :=
    IsRepresentedFamilyIn.names_uniform E.presentation E.flow_represented haP haPc
  have hS₁ : IsCeOpenFamilyIn P B fun d : (ℚ × ℕ) × ℚ ↦
      {w | (d.2 : ℝ) < dist w (G.φ (d.1.1 : ℝ) (P.ι d.1.2))} :=
    isCeOpenFamilyIn_lt_dist E.presentation (w₀ := fun qi : ℚ × ℕ ↦ G.φ (qi.1 : ℝ) (P.ι qi.2))
      (a := fun qi ↦ b₁ qi.1 qi.2) (fun qi ↦ hb₁ qi.1 qi.2) hb₁c
  have hS₂ : IsCeOpenFamilyIn P B fun d : (ℚ × ℕ) × ℚ ↦
      {w | (d.2 : ℝ) < dist w (G.φ (d.1.1 : ℝ) (E.pIdx d.1.2))} :=
    isCeOpenFamilyIn_lt_dist E.presentation
      (w₀ := fun qk : ℚ × ℕ ↦ G.φ (qk.1 : ℝ) (E.pIdx qk.2))
      (a := fun qk ↦ b₂ qk.1 qk.2) (fun qk ↦ hb₂ qk.1 qk.2) hb₂c
  have hA := E.flow_represented.preimage_ceOpen hS₁
  have hB := E.flow_represented.preimage_ceOpen hS₂
  have pi : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have pT : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have pkq : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have hneg : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ -((w.2 : ℕ) : ℚ) :=
    ComputableReals.computable_ratNeg.comp
      (ComputableReals.computable_natCastRat.comp Computable.snd)
  have hg₁ : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦
      (-((w.2 : ℕ) : ℚ), ((-((w.2 : ℕ) : ℚ), w.1.2.2.1), ρ)) :=
    hneg.pair ((hneg.pair pi).pair (Computable.const ρ))
  have hp : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ decide (w.2 ≤ w.1.2.2.2.1) :=
    (Primrec.nat_le.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.snd.comp Primrec.fst))))).decide.to_comp
  have hO₁ := ((hA.comp hg₁).ite
    (p := fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦ w.2 ≤ w.1.2.2.2.1) hp).iUnion
  have hg₂ : Computable fun w : (ℕ × ℚ × ℕ × ℕ × ℕ) × ℕ ↦
      (-((w.1.2.2.2.1 + w.2 : ℕ) : ℚ), ((-((w.2 : ℕ) : ℚ), w.1.2.2.2.2), ρ)) :=
    (ComputableReals.computable_ratNeg.comp (ComputableReals.computable_natCastRat.comp
      (Primrec.nat_add.to_comp.comp pT Computable.snd))).pair
      ((hneg.pair pkq).pair (Computable.const ρ))
  have hO₂ := (hB.comp hg₂).iUnion
  refine ⟨_, hO₁.union hO₂, fun kp r i T kq ↦ ?_⟩
  ext z
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion,
    Set.mem_ite_empty_right, Set.mem_preimage, Set.mem_ofPred_eq, Rat.cast_neg,
    Rat.cast_natCast, Nat.cast_add, Rat.cast_add, shadowSetBackward]
  constructor
  · rintro ⟨hzK, hzS⟩
    refine ⟨hzK, ?_⟩
    by_contra hO
    simp only [not_or, not_exists, not_and, not_lt] at hO
    exact hzS ⟨hzK, hO.1, hO.2⟩
  · rintro ⟨hzK, hO⟩
    refine ⟨hzK, fun hzS ↦ ?_⟩
    rcases hO with ⟨j, hj, hlt⟩ | ⟨n, hlt⟩
    · exact absurd (hzS.2.1 j hj) (not_le.mpr hlt)
    · exact absurd (hzS.2.2 n) (not_le.mpr hlt)

/-- The reversed constraint sets lie in the plaque family of `Kplaque'_cc`. -/
theorem shadowSetBackward_subset_family (ρ : ℝ) (kp : ℕ) (r : ℚ) (i T kq : ℕ) (hr : 0 < r) :
    E.shadowSetBackward ρ r kp i T kq ⊆
      (fun kr : ℕ × ℚ ↦ if 0 < kr.2 then G.Kplaque' kr.2 (E.pIdx kr.1) else ∅) (kp, r) := by
  intro z hz
  change z ∈ (if 0 < r then G.Kplaque' r (E.pIdx kp) else ∅)
  rw [ite_eq_left hr]
  exact hz.1

/-- The certified search on the reversed constraint sets (`certified_localization` for the
stable plaque family of `Kplaque'_cc` and the violation sets of
`shadowSetBackward_compl_ceOpen`). Blueprint node `geo:localization` (reversed). -/
theorem shadowSetBackward_decoder (ρ : ℚ) :
    ∃ loc : ℕ × ℚ × ℕ × ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} loc ∧
      ∀ (kp : ℕ) (r : ℚ) (i T kq p : ℕ), 0 < r →
        (E.shadowSetBackward ρ r kp i T kq).Subsingleton →
        ∀ z₀ ∈ E.shadowSetBackward ρ r kp i T kq, (loc (kp, r, i, T, kq, p)).Dom ∧
          ∀ q ∈ loc (kp, r, i, T, kq, p), dist (P.ι q) z₀ < dyadicRadius p := by
  obtain ⟨O, hO, hOeq⟩ := E.shadowSetBackward_compl_ceOpen ρ
  have hK := E.Kplaque'_cc.comp (κ := ℕ × ℚ × ℕ × ℕ × ℕ)
    (Computable.fst.pair (Computable.fst.comp Computable.snd))
  obtain ⟨loc, hloc, hspec⟩ := certified_localization hK hO E.presentation
  have hre : Computable fun w : ℕ × ℚ × ℕ × ℕ × ℕ × ℕ ↦
      ((w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1), w.2.2.2.2.2) :=
    (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))).pair
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
            (Computable.snd.comp Computable.snd)))))))).pair
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp Computable.snd))))
  refine ⟨fun w ↦ loc ((w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1), w.2.2.2.2.2),
    hloc.comp hre.computableIn, fun kp r i T kq p hr hss z₀ hz₀ ↦ ?_⟩
  refine hspec (kp, r, i, T, kq) p _ (E.shadowSetBackward_subset_family ρ kp r i T kq hr) ?_
    hss z₀ hz₀
  change (if 0 < r then G.Kplaque' r (E.pIdx kp) else ∅) \ _ =
    (if 0 < r then G.Kplaque' r (E.pIdx kp) else ∅) ∩ _
  rw [ite_eq_left hr]
  exact hOeq kp r i T kq

/-- Time-reversed uniform decoder. Blueprint node `geo:localization` (reversed). -/
theorem localization_decoder_backward {Q : Set X} (hQ : IsCompact Q) (hQR : Q ⊆ G.Reg) :
    ∃ a : ℝ, 0 < a ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ρ : ℚ, 0 < ρ → 2 * G.L * ρ < a →
      ∃ loc : ℕ × ℚ × ℕ × ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle B} loc ∧
        ∀ (kp : ℕ) (r : ℚ) (i T kq p : ℕ), E.pIdx kp ∈ Q → 0 < r ∧ (r : ℝ) ≤ ε₀ →
          ∀ z₀ ∈ E.shadowSetBackward ρ r kp i T kq,
            (loc (kp, r, i, T, kq, p)).Dom ∧
              ∀ q ∈ loc (kp, r, i, T, kq, p), dist (P.ι q) z₀ < dyadicRadius p := by
  obtain ⟨a, ha, ε₀, hε₀, hsub⟩ := E.shadowSetBackward_subsingleton hQ hQR
  refine ⟨a, ha, ε₀, hε₀, fun ρ hρ hρa ↦ ?_⟩
  obtain ⟨loc, hloc, hspec⟩ := E.shadowSetBackward_decoder ρ
  exact ⟨loc, hloc, fun kp r i T kq p hkp hr z₀ hz₀ ↦
    hspec kp r i T kq p hr.1 (hsub ρ (by exact_mod_cast hρ.le) hρa kp r i T kq hkp hr) z₀ hz₀⟩

end EffectiveGeodesicData

end Kolmogorov.PointToSet
