/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface
import KolmogorovMathlib.Oracle.Encoding.Numerals
import KolmogorovMathlib.Oracle.PrefixComplexity.NatBounds
import KolmogorovMathlib.PointToSet.ComputableMetric.Points

/-!
# Extending an orbit description by itinerary data (geodesic blueprint, Chapter A)

The node `geo:orbit-extension` of `geodesic_upper_bound_blueprint.md`. An ideal point of a
Bowen ball of order `n` about `x` together with the itinerary of `x` through a fixed finite
ideal net on the next `m` steps determines, by an `A`-partial recursive search
(`isREIn_mem_bowenBall_inter_pullbacks`), an ideal point of the Bowen ball of order `n + m`
about `x`; so the orbit complexity of order `n + m` is at most that of order `n` plus
`m ⌈log₂ N⌉ + O(log n)` (`orbit_extension`, `orbit_extension_normalized`). The uniform orbit
names of the library (`exists_computable_orbit_names`) and the distance certificates of
`ComputableMetric/Points.lean` give the semidecidability
(`isComputableRealFamilyIn_dist_iterate_ideal`).
-/

namespace Kolmogorov.PointToSet

open Filter
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-! ### Uniform orbit names and semidecidable orbit conditions

The library's `exists_computable_orbit_names` (`BirkhoffComputability.lean`) gives Cauchy names
of ideal-point orbits computable uniformly in time, center and precision; this section combines
it with `isComputableRealFamilyIn_dist_names` (`ComputableMetric/Points.lean`) for
`geo:orbit-extension`. -/

section orbitNames

/-- Distances between orbit points of ideal points and ideal points form a relatively
computable real family, uniformly in the time and both indices.
Blueprint node `geo:orbit-extension` (auxiliary). -/
theorem isComputableRealFamilyIn_dist_iterate_ideal (P : Presentation X) (T : X → X)
    (A : Set ℕ) (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    IsComputableRealFamilyIn A fun d : ℕ × ℕ × ℕ ↦ dist (T^[d.1] (P.ι d.2.1)) (P.ι d.2.2) := by
  obtain ⟨a, hacomp, ha⟩ := exists_computable_orbit_names P T A hP hTA
  have h := isComputableRealFamilyIn_dist_names (ι := ℕ × ℕ) hP
    (x := fun ti ↦ T^[ti.1] (P.ι ti.2)) (a := a) (fun ti ↦ ha ti.1 ti.2) hacomp
  exact IsComputableRealFamilyIn.comp A _ h (fun d : ℕ × ℕ × ℕ ↦ ((d.1, d.2.1), d.2.2))
    ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd))

end orbitNames

/-! ### `geo:orbit-extension`: extending an orbit description by itinerary data -/

section orbitExtension

variable [CompactSpace X] (P : Presentation X) (T : X → X) (hT : Continuous T) (A : Set ℕ)
  (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T)

/-- A finite `ε/2`-net of ideal points exists and its indices are a finite constant of any
program. Blueprint node `geo:orbit-extension` (auxiliary). -/
theorem exists_finite_ideal_net {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∀ y : X, ∃ j ∈ s, dist (P.ι j) y < ε / 2 := by
  have hcover : (Set.univ : Set X) ⊆ ⋃ j : ℕ, Metric.ball (P.ι j) (ε / 2) := by
    intro y _
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp P.dense y (ε / 2) (half_pos hε)
    exact Set.mem_iUnion.mpr ⟨j, Metric.mem_ball.mpr hj⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun j ↦ Metric.ball (P.ι j) (ε / 2))
    (fun j ↦ Metric.isOpen_ball) hcover
  refine ⟨s, fun y ↦ ?_⟩
  obtain ⟨j, hj, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  exact ⟨j, hj, by rw [dist_comm]; exact Metric.mem_ball.mp hy⟩

omit [CompactSpace X] in
include hP hTA in
/-- Membership of an ideal point in a Bowen ball about another ideal point intersected with
finitely many pulled-back ideal balls is `A`-semidecidable, uniformly in the data.
Blueprint node `geo:orbit-extension` (auxiliary). -/
theorem isREIn_mem_bowenBall_inter_pullbacks :
    IsREIn A fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦
      P.ι d.1 ∈ bowenBall T d.2.2.1 (P.ι d.2.1) (d.2.2.2.1 : ℝ) ∧
        ∀ k : ℕ, ∀ h : k < d.2.2.2.2.length,
          T^[d.2.2.1 + k] (P.ι d.1) ∈ basicBall P (d.2.2.2.2.get ⟨k, h⟩) := by
  have hA : IsAdmissible P T (fun _ : Fin 0 ↦ fun _ ↦ (0 : ℝ)) A := ⟨hP, hTA, fun j ↦ j.elim0⟩
  -- projections of the data `d = (i, j, n, q, L)`
  have p1 : Primrec fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦ d.1 := Primrec.fst
  have p2 : Primrec fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦ d.2.1 := Primrec.fst.comp Primrec.snd
  have p3 : Primrec fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦ d.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have p4 : Primrec fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦ d.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have p5 : Primrec fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦ d.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  -- part A: the Bowen ball condition, with the order-zero case made vacuous
  have hltA := birkhoff_computableIn_lt A _ (birkhoff_computableIn_dist P T _ A hA)
  let fA : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) → (ℕ × ℕ × ℕ) × ℚ := fun d ↦
    ((d.2.2.1, d.2.1, d.1), if d.2.2.1 = 0 then 1 else d.2.2.2.1)
  have hfA : Primrec fA :=
    (p3.pair (p2.pair p1)).pair
      (Primrec.ite (Primrec.eq.comp p3 (Primrec.const 0)) (Primrec.const 1) p4)
  have hpartA : IsREIn A fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦
      P.ι d.1 ∈ bowenBall T d.2.2.1 (P.ι d.2.1) (d.2.2.2.1 : ℝ) := by
    have h := hltA.comp hfA.to_comp.computableIn
    have heq : (fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦
        bowenDist T (fA d).1.1 (P.ι (fA d).1.2.1) (P.ι (fA d).1.2.2) < ((fA d).2 : ℝ)) =
        fun d ↦ P.ι d.1 ∈ bowenBall T d.2.2.1 (P.ι d.2.1) (d.2.2.2.1 : ℝ) := by
      funext d
      apply propext
      by_cases hn : d.2.2.1 = 0
      · simp only [fA, hn, ↓reduceIte, bowen_ball_dense_zero, Set.mem_univ, iff_true,
          bowenDist, Finset.range_zero, Finset.sup_empty]
        norm_num
      · simp only [fA, hn, ↓reduceIte]
        exact (bowen_ball_dense_iff T _ (Nat.one_le_iff_ne_zero.mpr hn) _ _ _).symm
    rw [heq] at h
    exact h
  -- part B: the pulled-back basic balls along the list
  have hltB := birkhoff_computableIn_lt A _
    (isComputableRealFamilyIn_dist_iterate_ideal P T A hP hTA)
  have hF : IsREIn A fun w : (ℕ × ℕ) × ℕ × (ℕ × ℚ) ↦
      dist (T^[w.1.2 + w.2.1] (P.ι w.1.1)) (P.ι w.2.2.1) < (w.2.2.2 : ℝ) := by
    have hg : Primrec fun w : (ℕ × ℕ) × ℕ × (ℕ × ℚ) ↦
        ((w.1.2 + w.2.1, w.1.1, w.2.2.1), w.2.2.2) :=
      ((Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
        ((Primrec.fst.comp Primrec.fst).pair
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact hltB.comp hg.to_comp.computableIn
  have hpartB : IsREIn A fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦
      ∀ k : ℕ, ∀ h : k < d.2.2.2.2.length,
        T^[d.2.2.1 + k] (P.ι d.1) ∈ basicBall P (d.2.2.2.2.get ⟨k, h⟩) := by
    have hg : Primrec fun d : ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) ↦ ((d.1, d.2.2.1), d.2.2.2.2) :=
      (p1.pair p3).pair p5
    exact hF.list_forall_get.comp hg.to_comp.computableIn
  exact hpartA.and hpartB

omit [CompactSpace X] in
/-- The relative partial recursive search of `geo:orbit-extension`: from an ideal index `i`,
an order `n` and a numeral `J` encoding an itinerary of net indices (base `N`, leading
digit `1`), it finds an ideal point of the `ε`-Bowen ball of `P.ι i` of order `n` whose
further orbit follows the itinerary within `ε / 2`. -/
private lemma exists_extension_decoder (_hT : Continuous T) (hP : ComputablePresentationIn P A)
    (hTA : IsRepresentedMapIn P P A T) {N : ℕ} (_hN : 2 ≤ N) (l : List ℕ) (ε : ℚ) :
    ∃ F : ℕ × ℕ × ℕ →. ℕ, PartrecIn {charOracle A} F ∧
      (∀ i n J i', i' ∈ F (i, n, J) → ∃ m, N ^ m ≤ J ∧ J < N ^ (m + 1) ∧
        P.ι i' ∈ bowenBall T n (P.ι i) (ε : ℝ) ∧
        ∀ k < m, T^[n + k] (P.ι i') ∈ basicBall P (l.getD (J / N ^ k % N) 0, ε / 2)) ∧
      (∀ i n J m i', N ^ m ≤ J → J < N ^ (m + 1) →
        P.ι i' ∈ bowenBall T n (P.ι i) (ε : ℝ) →
        (∀ k < m, T^[n + k] (P.ι i') ∈ basicBall P (l.getD (J / N ^ k % N) 0, ε / 2)) →
        (F (i, n, J)).Dom) := by
  have hΦ := isREIn_mem_bowenBall_inter_pullbacks P T A hP hTA
  -- the itinerary list read off a numeral `J` with `m` digits
  let itin : ℕ × ℕ → List (ℕ × ℚ) := fun Jm ↦
    (List.range Jm.2).map fun k ↦ (l.getD (digitAt N Jm.1 k) 0, ε / 2)
  have hitin : Primrec itin :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (((Primrec.list_getD 0).comp (Primrec.const l)
        ((primrec_digitAt N).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)).pair
        (Primrec.const (ε / 2)))
  have hitin_len : ∀ J m, (itin (J, m)).length = m := by
    intro J m
    simp [itin]
  have hitin_get : ∀ J m k (h : k < (itin (J, m)).length),
      (itin (J, m)).get ⟨k, h⟩ = (l.getD (J / N ^ k % N) 0, ε / 2) := by
    intro J m k h
    simp [itin, List.get_eq_getElem, digitAt_eq]
  -- the data of the semidecidable condition, in the format of the pullback lemma
  let g : (ℕ × ℕ × ℕ) × (ℕ × ℕ) → ℕ × ℕ × ℕ × ℚ × List (ℕ × ℚ) := fun w ↦
    (w.2.2, w.1.1, w.1.2.1, ε, itin (w.1.2.2, w.2.1))
  have hg : Primrec g :=
    (Primrec.snd.comp Primrec.snd).pair ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair ((Primrec.const ε).pair
        (hitin.comp ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair
          (Primrec.fst.comp Primrec.snd))))))
  -- the decidable check that `m` is the number of digits of `J`
  let decB : (ℕ × ℕ × ℕ) × (ℕ × ℕ) → Bool := fun w ↦
    (natPowRec N w.2.1 - w.1.2.2 == 0) && !(natPowRec N (w.2.1 + 1) - w.1.2.2 == 0)
  have hdecB : Primrec decB := by
    have hJ : Primrec fun w : (ℕ × ℕ × ℕ) × (ℕ × ℕ) ↦ w.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hm : Primrec fun w : (ℕ × ℕ × ℕ) × (ℕ × ℕ) ↦ w.2.1 := Primrec.fst.comp Primrec.snd
    refine Primrec.and.comp (Primrec.beq.comp (Primrec.nat_sub.comp
      ((primrec_natPowRec N).comp hm) hJ) (Primrec.const 0)) (Primrec.not.comp ?_)
    exact Primrec.beq.comp (Primrec.nat_sub.comp
      ((primrec_natPowRec N).comp (Primrec.succ.comp hm)) hJ) (Primrec.const 0)
  have hdecB_iff : ∀ w, decB w = true ↔ N ^ w.2.1 ≤ w.1.2.2 ∧ w.1.2.2 < N ^ (w.2.1 + 1) := by
    intro w
    simp only [decB, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq, Nat.sub_eq_zero_iff_le, not_le, natPowRec_eq]
  have hdec : IsREIn A fun w : (ℕ × ℕ × ℕ) × (ℕ × ℕ) ↦ decB w = true :=
    isREIn_of_computable_decide (hdecB.to_comp.of_eq fun w ↦ Bool.decide_eq_true.symm)
  -- the search predicate and its enumeration
  have hΨ : IsREIn A fun w : (ℕ × ℕ × ℕ) × (ℕ × ℕ) ↦ decB w = true ∧
      (P.ι (g w).1 ∈ bowenBall T (g w).2.2.1 (P.ι (g w).2.1) ((g w).2.2.2.1 : ℝ) ∧
        ∀ k : ℕ, ∀ h : k < (g w).2.2.2.2.length,
          T^[(g w).2.2.1 + k] (P.ι (g w).1) ∈ basicBall P ((g w).2.2.2.2.get ⟨k, h⟩)) :=
    hdec.and (hΦ.comp hg.to_comp.computableIn)
  obtain ⟨e, he, henum⟩ := (relative_enumeration A _).mp hΨ
  let sel : (ℕ × ℕ × ℕ) × Option ((ℕ × ℕ × ℕ) × (ℕ × ℕ)) → Option ℕ := fun q ↦
    q.2.bind fun w ↦
      if Encodable.encode w.1 = Encodable.encode q.1 then some w.2.2 else none
  have hsel : Primrec sel :=
    Primrec.option_bind Primrec.snd
      (Primrec.ite (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.encode.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.const none))
  refine ⟨fun x ↦ Nat.rfindOpt fun t ↦ sel (x, e t), ?_, ?_, ?_⟩
  · exact PartrecIn.rfindOpt (ComputableIn₂.mk
      (hsel.to_comp.computableIn.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd))))
  · intro i n J i' hi'
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hi'
    rw [Option.mem_def] at ht
    obtain ⟨w, hw, hw'⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨⟨i₀, n₀, J₀⟩, m, i₁⟩ := w
    split_ifs at hw' with hkey
    · have hkey' : (i₀, n₀, J₀) = (i, n, J) := Encodable.encode_injective hkey
      simp only [Prod.mk.injEq] at hkey'
      obtain ⟨rfl, rfl, rfl⟩ := hkey'
      have hi₁ : i₁ = i' := Option.some_injective _ hw'
      subst hi₁
      obtain ⟨hdecw, hB, hL⟩ := (henum _).mpr ⟨t, hw⟩
      obtain ⟨h1, h2⟩ := (hdecB_iff _).mp hdecw
      refine ⟨m, h1, h2, hB, fun k hk ↦ ?_⟩
      have hk' : k < (itin (J₀, m)).length := by rw [hitin_len]; exact hk
      have := hL k hk'
      rwa [hitin_get] at this
  · intro i n J m i' h1 h2 hB hL
    have hΨw : decB ((i, n, J), (m, i')) = true ∧
        (P.ι i' ∈ bowenBall T n (P.ι i) (ε : ℝ) ∧
          ∀ k : ℕ, ∀ h : k < (itin (J, m)).length,
            T^[n + k] (P.ι i') ∈ basicBall P ((itin (J, m)).get ⟨k, h⟩)) := by
      refine ⟨(hdecB_iff _).mpr ⟨h1, h2⟩, hB, fun k hk ↦ ?_⟩
      rw [hitin_get]
      exact hL k (by rwa [hitin_len] at hk)
    obtain ⟨t, ht⟩ := (henum _).mp hΨw
    refine Nat.rfindOpt_dom.mpr ⟨t, i', ?_⟩
    simp [sel, ht]

include hT hP hTA in
/-- Extending an `ε`-orbit description of length `n` to a `2ε`-description of length
`n + m` costs at most `m ⌈log₂ N⌉` bits of itinerary data plus logarithmic overhead, where
`N` is the size of a fixed `ε/2`-net of ideal points.
Blueprint node `geo:orbit-extension`. -/
theorem orbit_extension {ε : ℚ} (hε : 0 < ε) :
    ∃ N c : ℕ, ∀ y : X, ∀ n m : ℕ, 1 ≤ n →
      (orbitComplexityNat P T A y (n + m) (2 * (ε : ℝ)) : ℝ) ≤
        orbitComplexityNat P T A y n (ε : ℝ) + (m : ℝ) * (Nat.clog 2 N : ℝ) +
          2 * Real.logb 2 ((n : ℝ) + 1) + 2 * Real.logb 2 ((m : ℝ) + 1) + c := by
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨s, hs⟩ := exists_finite_ideal_net P hε'
  set l := s.toList with hl
  have hnet : ∀ y : X, ∃ a < l.length, dist (P.ι (l.getD a 0)) y < (ε : ℝ) / 2 := by
    intro y
    obtain ⟨j, hj, hjy⟩ := hs y
    obtain ⟨a, ha, hja⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hj)
    exact ⟨a, ha, by rw [List.getD_eq_getElem _ _ ha, hja]; exact hjy⟩
  have hlog_nonneg : ∀ k : ℕ, 0 ≤ Real.logb 2 ((k : ℝ) + 1) := fun k ↦
    Real.logb_nonneg one_lt_two (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  by_cases hN : l.length ≤ 1
  · -- degenerate case: the whole space has diameter below `ε`
    refine ⟨l.length, 0, fun y n m hn ↦ ?_⟩
    have hdiam : ∀ y z : X, dist y z < (ε : ℝ) := by
      intro y z
      obtain ⟨a, ha, hay⟩ := hnet y
      obtain ⟨b, hb, hbz⟩ := hnet z
      have hab : a = b := by omega
      subst hab
      calc dist y z ≤ dist y (P.ι (l.getD a 0)) + dist (P.ι (l.getD a 0)) z :=
            dist_triangle _ _ _
        _ < (ε : ℝ) / 2 + (ε : ℝ) / 2 := by
            rw [dist_comm] at hay
            exact add_lt_add hay hbz
        _ = ε := by ring
    obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A y hT n hε'
    have hmem : P.ι i ∈ bowenBall T (n + m) y (2 * (ε : ℝ)) :=
      mem_bowenBall_iff.2 fun k _ ↦ (hdiam _ _).trans (by linarith)
    have hle := orbitComplexityNat_le P T A y hmem
    rw [hiK] at hle
    have hle' : (orbitComplexityNat P T A y (n + m) (2 * (ε : ℝ)) : ℝ) ≤
        orbitComplexityNat P T A y n ε := by exact_mod_cast hle
    have h1 : 0 ≤ (m : ℝ) * (Nat.clog 2 l.length : ℝ) := by positivity
    have h2 := hlog_nonneg n
    have h3 := hlog_nonneg m
    push_cast
    linarith
  · -- main case: a net with at least two points
    rw [not_le] at hN
    set N := l.length with hNdef
    have hN2 : 2 ≤ N := hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    obtain ⟨F, hF, hFsound, hFdom⟩ := exists_extension_decoder P T A hT hP hTA hN2 l ε
    obtain ⟨c₁, hc₁⟩ := oracleNatComplexity_le_log_add_loglog A
    obtain ⟨c₂, hc₂⟩ := oracle_tuple_bounds_overhead A
    -- the two-input decompressor on bit strings
    let F' : List BitString →. BitString := fun xs ↦
      (F (bitsToNat (decodeFirst (xs.getD 0 [])), bitsToNat (decodeSecond (xs.getD 0 [])),
        bitsToNat (xs.getD 1 []))).map natBits
    have hF' : PartrecIn {charOracle A} F' := by
      have h0 : Computable fun xs : List BitString ↦ xs.getD 0 [] :=
        (Primrec.list_getD []).to_comp.comp Computable.id (Computable.const 0)
      have h1 : Computable fun xs : List BitString ↦ xs.getD 1 [] :=
        (Primrec.list_getD []).to_comp.comp Computable.id (Computable.const 1)
      refine PartrecIn.map (hF.comp ?_)
        (ComputableIn₂.mk (natBits_computable.comp Computable.snd).computableIn)
      exact ((bitsToNat_computable.comp (decodeFirst_computable.comp h0)).pair
        ((bitsToNat_computable.comp (decodeSecond_computable.comp h0)).pair
          (bitsToNat_computable.comp h1))).computableIn
    obtain ⟨c₃, hc₃⟩ := oracle_tuple_bounds_composition A 2 F' hF'
    have hclog : Real.logb 2 (N : ℝ) ≤ (Nat.clog 2 N : ℝ) := by
      have h := Real.logb_le_logb_of_le one_lt_two hN0
        (by exact_mod_cast Nat.le_pow_clog one_lt_two N : (N : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 N)
      rwa [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at h
    have hclog0 : (0 : ℝ) ≤ Nat.clog 2 N := Nat.cast_nonneg _
    refine ⟨N, ⌈(c₁ + c₂ + c₃ + 1 + 2 * Real.logb 2 ((Nat.clog 2 N : ℝ) + 2) : ℝ)⌉₊,
      fun y n m hn ↦ ?_⟩
    -- a realizer of the `ε`-orbit complexity of order `n`
    obtain ⟨i, hi, hiK⟩ := orbitComplexityNat_attained P T A y hT n hε'
    -- the itinerary: net indices along the orbit of `y` at times `n, …, n + m - 1`
    choose a ha hay using fun k : ℕ ↦ hnet (T^[n + k] y)
    let D : List ℕ := (List.range m).map a
    have hD : ∀ d ∈ D, d < N := by
      intro d hd
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hd
      exact ha k
    have hDlen : D.length = m := by simp [D]
    set J := Nat.ofDigits N (D ++ [1]) with hJdef
    have hJ := ofDigits_append_one_bounds hN2 D hD
    rw [hDlen] at hJ
    have hJlt : J < N ^ (m + 1) := by
      have : 2 * N ^ m ≤ N ^ (m + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right _ hN2 |>.trans (le_of_eq (mul_comm _ _))
      omega
    have hdig : ∀ k < m, J / N ^ k % N = a k := by
      intro k hk
      rw [hJdef, ofDigits_append_one_digit hN2 D hD (by omega : k < D.length)]
      simp [D]
    -- an ideal point certified by the search exists (density of ideal points)
    have hU : ∃ i', P.ι i' ∈ bowenBall T n (P.ι i) (ε : ℝ) ∧
        ∀ k < m, T^[n + k] (P.ι i') ∈ basicBall P (l.getD (a k) 0, ε / 2) := by
      let U : Set X := bowenBall T n (P.ι i) ε ∩
        ⋂ k ∈ Finset.range m, (T^[n + k]) ⁻¹' Metric.ball (P.ι (l.getD (a k) 0)) ((ε : ℝ) / 2)
      have hUopen : IsOpen U :=
        (bowen_ball_dense_open T hT n _ _).inter
          (isOpen_biInter_finset fun k _ ↦ Metric.isOpen_ball.preimage (hT.iterate _))
      have hyU : y ∈ U := by
        refine ⟨mem_bowenBall_symm hi, Set.mem_iInter₂.mpr fun k _ ↦ ?_⟩
        rw [Set.mem_preimage, Metric.mem_ball, dist_comm]
        exact hay k
      obtain ⟨i', hi'⟩ := P.dense.exists_mem_open hUopen ⟨y, hyU⟩
      refine ⟨i', hi'.1, fun k hk ↦ ?_⟩
      have h := Set.mem_iInter₂.mp hi'.2 k (Finset.mem_range.mpr hk)
      change T^[n + k] (P.ι i') ∈ Metric.ball (P.ι (l.getD (a k) 0)) (((ε / 2 : ℚ)) : ℝ)
      push_cast
      exact h
    obtain ⟨i', hi'B, hi'L⟩ := hU
    have hdom : (F (i, n, J)).Dom :=
      hFdom i n J m i' hJ.1 hJlt hi'B fun k hk ↦ by rw [hdig k hk]; exact hi'L k hk
    have hi''F : (F (i, n, J)).get hdom ∈ F (i, n, J) := Part.get_mem hdom
    set i'' := (F (i, n, J)).get hdom with hi''def
    obtain ⟨m', hm'1, hm'2, hB, hL⟩ := hFsound i n J i'' hi''F
    have hm' : m' = m := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : N ^ (m' + 1) ≤ N ^ m := Nat.pow_le_pow_right (by omega) h
        omega
      · have : N ^ (m + 1) ≤ N ^ m' := Nat.pow_le_pow_right (by omega) h
        omega
    subst hm'
    -- the output shadows `y` on `[0, n + m')` within `2 ε`
    have hmem : P.ι i'' ∈ bowenBall T (n + m') y (2 * (ε : ℝ)) := by
      rw [mem_bowenBall_iff]
      intro k hk
      by_cases hkn : k < n
      · have h1 := mem_bowenBall_iff.1 hi k hkn
        have h2 := mem_bowenBall_iff.1 hB k hkn
        calc dist (T^[k] y) (T^[k] (P.ι i''))
            ≤ dist (T^[k] y) (T^[k] (P.ι i)) + dist (T^[k] (P.ι i)) (T^[k] (P.ι i'')) :=
              dist_triangle _ _ _
          _ < ε + ε := add_lt_add h1 h2
          _ = 2 * ε := by ring
      · obtain ⟨k', rfl⟩ : ∃ k', k = n + k' := ⟨k - n, by omega⟩
        have hk' : k' < m' := by omega
        have h1 := hL k' hk'
        rw [hdig k' hk'] at h1
        have h1' : dist (T^[n + k'] (P.ι i'')) (P.ι (l.getD (a k') 0)) < (ε : ℝ) / 2 := by
          have h := Metric.mem_ball.mp h1
          push_cast at h
          exact h
        have h2 := hay k'
        calc dist (T^[n + k'] y) (T^[n + k'] (P.ι i''))
            ≤ dist (T^[n + k'] y) (P.ι (l.getD (a k') 0)) +
              dist (P.ι (l.getD (a k') 0)) (T^[n + k'] (P.ι i'')) := dist_triangle _ _ _
          _ < (ε : ℝ) / 2 + (ε : ℝ) / 2 :=
              add_lt_add (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h1')
          _ ≤ 2 * ε := by linarith
    -- the complexity of the output
    have hKle : orbitComplexityNat P T A y (n + m') (2 * (ε : ℝ)) ≤ oracleNatComplexity A i'' :=
      orbitComplexityNat_le P T A y hmem
    have hcomp : oracleNatComplexity A i'' ≤
        oraclePairComplexity A i n + oracleNatComplexity A J + c₃ := by
      have hx : natBits i'' ∈ F' [pairCode (natBits i) (natBits n), natBits J] := by
        simp only [F', List.getD_cons_zero, List.getD_cons_succ, decodeFirst_pairCode,
          decodeSecond_pairCode]
        rw [show bitsToNat (natBits i) = i from bitsToNat_bits i,
          show bitsToNat (natBits n) = n from bitsToNat_bits n,
          show bitsToNat (natBits J) = J from bitsToNat_bits J]
        exact (Part.mem_map_iff _).mpr ⟨i'', hi''F, rfl⟩
      have h := hc₃ _ _ rfl hx
      simpa [oraclePairComplexity, oracleNatComplexity, add_assoc] using h
    -- real arithmetic
    have hKn := hc₂ i n
    have hKJ := hc₁ J
    have hJreal : ((J : ℝ) + 1) ≤ 2 * (N : ℝ) ^ m' := by exact_mod_cast hJ.2
    have hJlog : Real.logb 2 ((J : ℝ) + 1) ≤ 1 + (m' : ℝ) * (Nat.clog 2 N : ℝ) := by
      calc Real.logb 2 ((J : ℝ) + 1) ≤ Real.logb 2 (2 * (N : ℝ) ^ m') :=
            Real.logb_le_logb_of_le one_lt_two (by positivity) hJreal
        _ = 1 + (m' : ℝ) * Real.logb 2 (N : ℝ) := by
            rw [Real.logb_mul two_ne_zero (pow_ne_zero _ hN0.ne'), Real.logb_self_eq_one one_lt_two,
              Real.logb_pow]
        _ ≤ 1 + (m' : ℝ) * (Nat.clog 2 N : ℝ) := by
            gcongr
    have hJlog0 : 0 ≤ Real.logb 2 ((J : ℝ) + 1) := hlog_nonneg J
    have hloglog : Real.logb 2 (Real.logb 2 ((J : ℝ) + 1) + 1) ≤
        Real.logb 2 ((m' : ℝ) + 1) + Real.logb 2 ((Nat.clog 2 N : ℝ) + 2) := by
      have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg _
      have hle : Real.logb 2 ((J : ℝ) + 1) + 1 ≤ ((m' : ℝ) + 1) * ((Nat.clog 2 N : ℝ) + 2) := by
        nlinarith
      calc Real.logb 2 (Real.logb 2 ((J : ℝ) + 1) + 1)
          ≤ Real.logb 2 (((m' : ℝ) + 1) * ((Nat.clog 2 N : ℝ) + 2)) :=
            Real.logb_le_logb_of_le one_lt_two (by linarith) hle
        _ = Real.logb 2 ((m' : ℝ) + 1) + Real.logb 2 ((Nat.clog 2 N : ℝ) + 2) :=
            Real.logb_mul (by linarith) (by linarith)
    have hceil := Nat.le_ceil (c₁ + c₂ + c₃ + 1 + 2 * Real.logb 2 ((Nat.clog 2 N : ℝ) + 2))
    have hKle' : (orbitComplexityNat P T A y (n + m') (2 * (ε : ℝ)) : ℝ) ≤
        oracleNatComplexity A i'' := by exact_mod_cast hKle
    have hcomp' : (oracleNatComplexity A i'' : ℝ) ≤
        oraclePairComplexity A i n + oracleNatComplexity A J + c₃ := by exact_mod_cast hcomp
    have hiK' : (oracleNatComplexity A i : ℝ) = orbitComplexityNat P T A y n ε := by
      exact_mod_cast hiK
    linarith

include hT hP hTA in
/-- Normalized form used in `geo:section-point-mixed`: along any `n_k → ∞` and
`m_k ≤ (c - 1) n_k`, the extension penalty per unit of `n_k` is at most
`(c - 1) ⌈log₂ N⌉ + o(1)`. Blueprint node `geo:orbit-extension`. -/
theorem orbit_extension_normalized {ε : ℚ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (y : X) (nseq mseq : ℕ → ℕ) (c : ℝ), 1 < c →
      Tendsto nseq atTop atTop → (∀ k, (mseq k : ℝ) ≤ (c - 1) * nseq k) →
      limsup (fun k ↦ ((orbitComplexityNat P T A y (nseq k + mseq k) (2 * (ε : ℝ)) : ℝ) -
          (orbitComplexityNat P T A y (nseq k) (ε : ℝ) : ℝ)) / (nseq k : ℝ)) atTop ≤
        (c - 1) * (Nat.clog 2 N : ℝ) := by
  obtain ⟨N, c₀, hNc⟩ := orbit_extension P T hT A hP hTA hε
  refine ⟨N, fun y nseq mseq c hc hn hm ↦ ?_⟩
  set u : ℕ → ℝ := fun k ↦ ((orbitComplexityNat P T A y (nseq k + mseq k) (2 * (ε : ℝ)) : ℝ) -
      (orbitComplexityNat P T A y (nseq k) (ε : ℝ) : ℝ)) / (nseq k : ℝ) with hu
  have hlogN : (0 : ℝ) ≤ Nat.clog 2 N := Nat.cast_nonneg _
  have hc1 : 0 < c - 1 := by linarith
  set err : ℕ → ℝ := fun n ↦
    (4 * Real.logb 2 ((n : ℝ) + 1) + (2 * Real.logb 2 c + c₀)) / (n : ℝ) with herr
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hlog := (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-1) 1 one_ne_zero).comp
      hshift
    have hlog' : Tendsto (fun n : ℕ ↦ Real.logb 2 ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hlog
    have hK : Tendsto (fun n : ℕ ↦ (2 * Real.logb 2 c + c₀) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [herr, zero_add, mul_zero, add_div, mul_div_assoc] using (hlog'.const_mul 4).add hK
  set v : ℕ → ℝ := fun k ↦ (c - 1) * (Nat.clog 2 N : ℝ) + err (nseq k) with hv
  have hvlim : Tendsto v atTop (𝓝 ((c - 1) * (Nat.clog 2 N : ℝ))) := by
    have := (herr0.comp hn).const_add ((c - 1) * (Nat.clog 2 N : ℝ))
    simpa [hv, Function.comp_def] using this
  have hev : ∀ᶠ k in atTop, u k ≤ v k := by
    filter_upwards [hn.eventually_ge_atTop 1] with k hk
    have hnpos : (0 : ℝ) < nseq k := by exact_mod_cast hk
    have hbound := hNc y (nseq k) (mseq k) hk
    have hm' := hm k
    have hmN : (mseq k : ℝ) * (Nat.clog 2 N : ℝ) ≤ (c - 1) * nseq k * (Nat.clog 2 N : ℝ) :=
      mul_le_mul_of_nonneg_right hm' hlogN
    have hlogm : Real.logb 2 ((mseq k : ℝ) + 1) ≤
        Real.logb 2 c + Real.logb 2 ((nseq k : ℝ) + 1) := by
      rw [← Real.logb_mul (by linarith) (by linarith)]
      apply Real.logb_le_logb_of_le one_lt_two (by linarith)
      linarith
    have hR : v k = ((c - 1) * (Nat.clog 2 N : ℝ) * nseq k +
        (4 * Real.logb 2 ((nseq k : ℝ) + 1) + (2 * Real.logb 2 c + c₀))) / (nseq k : ℝ) := by
      simp only [hv, herr]
      field_simp
    rw [hR]
    apply div_le_div_of_nonneg_right _ hnpos.le
    linarith
  by_cases hcob : IsCoboundedUnder (· ≤ ·) atTop u
  · calc limsup u atTop ≤ limsup v atTop := limsup_le_limsup hev hcob hvlim.isBoundedUnder_le
      _ = _ := hvlim.limsup_eq
  · have hnb : ¬ BddBelow {a : ℝ | ∀ᶠ n in atTop, u n ≤ a} := hcob
    rw [limsup_eq, Real.sInf_of_not_bddBelow hnb]
    exact mul_nonneg hc1.le hlogN

end orbitExtension

end Kolmogorov.PointToSet
