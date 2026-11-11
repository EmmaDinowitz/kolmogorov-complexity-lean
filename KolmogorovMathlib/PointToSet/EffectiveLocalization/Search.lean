/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.Compact
import KolmogorovMathlib.PointToSet.ComputableMetric.Represented

/-!
# The certified localization search

The one search every effective decoder of the geodesic program instantiates. Let `K` be a
computably compact family and `O` a c.e. open family of "violation sets", both indexed by a
primcodable type `κ`, and let `S ⊆ K k` be a constraint set whose complement inside `K k` is
`K k ∩ O k`. The containment `K k ⊆ O k ∪ ball (ι c) 2⁻ᵖ` is semidecidable uniformly in the
index `k`, the precision `p` and the ideal center `c`
(`IsComputablyCompactFamilyIn.subset_ceOpen_isREIn`), so dovetailing over `c` gives one partial
recursive program which halts whenever `S` is a
subsingleton `{z₀}` (a center within `2⁻ᵖ` of `z₀` certifies) and then outputs a
`2⁻ᵖ`-approximation of `z₀`, since `z₀ ∉ O k` (`certified_localization`).

* `certified_localization_map`: the same search with the target ball replaced by its preimage
  under a map `f k` represented on a domain `D k ⊇ K k`; the output approximates `f k z₀`.
* `certified_localization_point`: a point located by such a program along a computable input
  sequence is a computable point.

No dynamics enter; the geodesic chapters supply the families. Blueprint nodes
`eff:certified-localization` and `eff:certified-localization-map`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The rational dyadic radius casts to `dyadicRadius`. -/
theorem cast_inv_two_pow_eq_dyadicRadius (p : ℕ) :
    (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) = dyadicRadius p := by
  rw [dyadicRadius, inv_pow]
  push_cast
  rfl

/-- The certified localization search. For a computably compact family `K`, a c.e. open family
`O` of violation sets and a computable presentation, one `A`-partial recursive program `loc`
searches, on input `(k, p)`, over ideal centers `c` for the semidecidable certificate
`K k ⊆ O k ∪ ball (ι c) 2⁻ᵖ`. Whenever a constraint set `S ⊆ K k` with `K k \ S = K k ∩ O k`
is a subsingleton, the program halts on `(k, p)` and outputs an ideal index within `2⁻ᵖ` of
every point of `S`. Blueprint node `eff:certified-localization`. -/
theorem certified_localization {κ : Type*} [Primcodable κ] {P : Presentation X} {A : Set ℕ}
    {K : κ → Set X} (hK : IsComputablyCompactFamilyIn P A K)
    {O : κ → Set X} (hO : IsCeOpenFamilyIn P A O) (hP : ComputablePresentationIn P A) :
    ∃ loc : κ × ℕ →. ℕ, PartrecIn {charOracle A} loc ∧
      ∀ k p, ∀ S : Set X, S ⊆ K k → K k \ S = K k ∩ O k → S.Subsingleton →
        ∀ z₀ ∈ S, (loc (k, p)).Dom ∧ ∀ q ∈ loc (k, p), dist (P.ι q) z₀ < dyadicRadius p := by
  -- the certificate family: the violation set together with a dyadic ball about an ideal point
  have hbidx : Computable fun w : (κ × ℕ) × ℕ ↦ (w.2, (2 ^ w.1.2 : ℚ)⁻¹) :=
    Computable.snd.pair (computable_rat_inv_two_pow.comp (Computable.snd.comp Computable.fst))
  have hU : IsCeOpenFamilyIn P A fun w : (κ × ℕ) × ℕ ↦
      O w.1.1 ∪ Metric.ball (P.ι w.2) (((2 ^ w.1.2 : ℚ)⁻¹ : ℚ) : ℝ) :=
    (hO.comp (Computable.fst.comp Computable.fst)).union
      ((isCeOpenFamilyIn_ball P A hP).comp hbidx)
  have hG : IsREIn A fun w : (κ × ℕ) × ℕ ↦
      K w.1.1 ⊆ O w.1.1 ∪ Metric.ball (P.ι w.2) (((2 ^ w.1.2 : ℚ)⁻¹ : ℚ) : ℝ) :=
    (hK.subset_ceOpen_isREIn hU).comp
      ((Computable.fst.comp Computable.fst).pair Computable.id).computableIn
  obtain ⟨loc, hloc, hdom, hsound⟩ := hG.exists_partrecIn_choice
  refine ⟨loc, hloc, fun k p S hSK hOeq hss z₀ hz₀ ↦ ?_⟩
  have hz₀K : z₀ ∈ K k := hSK hz₀
  have hz₀O : z₀ ∉ O k := fun h ↦ by
    have hmem : z₀ ∈ K k \ S := by
      rw [hOeq]
      exact ⟨hz₀K, h⟩
    exact hmem.2 hz₀
  have hrad := cast_inv_two_pow_eq_dyadicRadius p
  constructor
  · refine (hdom _).mpr ?_
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp P.dense z₀ (dyadicRadius p) (dyadicRadius_pos p)
    refine ⟨c, fun z hz ↦ ?_⟩
    by_cases hzS : z ∈ S
    · have hzz : z = z₀ := hss hzS hz₀
      refine Or.inr (Metric.mem_ball.mpr ?_)
      rw [hzz, hrad]
      exact hc
    · have hmem : z ∈ K k ∩ O k := by
        rw [← hOeq]
        exact ⟨hz, hzS⟩
      exact Or.inl hmem.2
  · intro q hq
    rcases hsound _ q hq hz₀K with h | h
    · exact (hz₀O h).elim
    · have h' : dist z₀ (P.ι q) < (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := h
      rw [hrad] at h'
      rw [dist_comm]
      exact h'

/-- The certified localization search through a represented map. The data of
`certified_localization`, together with maps `f k : X → Y` represented on domains `D k` by one
relation `R` enumerable uniformly in `k` (the shape of `IsRepresentedOnIn` with the index
adjoined). The target ball is replaced by the c.e. open set of input balls `b` with a listed
output ball `R (k, (b, c'))` certified inside `ball (ι c) 2⁻ᵖ`; whenever `K k ⊆ D k` and the
constraint set is a subsingleton, the program halts on `(k, p)` and outputs an ideal index of
`Q` within `2⁻ᵖ` of `f k z₀`. Blueprint node `eff:certified-localization-map`. -/
theorem certified_localization_map {κ : Type*} [Primcodable κ] {P : Presentation X}
    {Q : Presentation Y} {A : Set ℕ} {K : κ → Set X} (hK : IsComputablyCompactFamilyIn P A K)
    {O : κ → Set X} (hO : IsCeOpenFamilyIn P A O) (hQ : ComputablePresentationIn Q A)
    {D : κ → Set X} {f : κ → X → Y} {R : κ × ((ℕ × ℚ) × (ℕ × ℚ)) → Prop} (hR : IsREIn A R)
    (hRs : ∀ k b c, R (k, (b, c)) →
      0 < b.2 ∧ 0 < c.2 ∧ f k '' (basicBall P b ∩ D k) ⊆ basicBall Q c)
    (hRc : ∀ k, ∀ x ∈ D k, ∀ c, f k x ∈ basicBall Q c → ∃ b, R (k, (b, c)) ∧ x ∈ basicBall P b) :
    ∃ loc : κ × ℕ →. ℕ, PartrecIn {charOracle A} loc ∧
      ∀ k p, ∀ S : Set X, S ⊆ K k → K k \ S = K k ∩ O k → S.Subsingleton → K k ⊆ D k →
        ∀ z₀ ∈ S, (loc (k, p)).Dom ∧
          ∀ q ∈ loc (k, p), dist (Q.ι q) (f k z₀) < dyadicRadius p := by
  have hlt := birkhoff_computableIn_lt A _ hQ
  -- the pulled-back target ball: input balls with a listed output ball certified inside
  -- `ball (ι c) 2⁻ᵖ`
  let Ecert : (κ × ℕ × ℕ) × (ℕ × ℚ) → Prop := fun w ↦
    ∃ c' : ℕ × ℚ, R (w.1.1, (w.2, c')) ∧
      dist (Q.ι c'.1) (Q.ι w.1.2.1) < (((2 ^ w.1.2.2 : ℚ)⁻¹ - c'.2 : ℚ) : ℝ)
  have hEcert : IsREIn A Ecert := by
    have h1 : ComputableIn {charOracle A}
        fun v : ((κ × ℕ × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦ (v.1.1.1, (v.1.2, v.2)) :=
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd)).computableIn
    have h2 : ComputableIn {charOracle A}
        fun v : ((κ × ℕ × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
          ((v.2.1, v.1.1.2.1), (2 ^ v.1.1.2.2 : ℚ)⁻¹ - v.2.2) :=
      (((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))).pair
        (computable₂_ratSub.comp (computable_rat_inv_two_pow.comp
          (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))))
          (Computable.snd.comp Computable.snd))).computableIn
    exact IsREIn.exists ((hR.comp h1).and (hlt.comp h2))
  let V : κ × ℕ × ℕ → Set X := fun d ↦ ⋃ b ∈ {b | Ecert (d, b)}, basicBall P b
  have hV : IsCeOpenFamilyIn P A V := ⟨Ecert, hEcert, fun _ ↦ rfl⟩
  have hVsound : ∀ k c p z, z ∈ D k → z ∈ V (k, c, p) →
      dist (f k z) (Q.ι c) < dyadicRadius p := by
    intro k c p z hzD hzV
    obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hzV
    obtain ⟨c', hR', hcert⟩ := hb
    have hfz : f k z ∈ basicBall Q c' := (hRs k b c' hR').2.2 ⟨z, ⟨hzb, hzD⟩, rfl⟩
    have h1 : dist (f k z) (Q.ι c'.1) < c'.2 := hfz
    have h2 : dist (Q.ι c'.1) (Q.ι c) < (((2 ^ p : ℚ)⁻¹ - c'.2 : ℚ) : ℝ) := hcert
    rw [Rat.cast_sub, cast_inv_two_pow_eq_dyadicRadius] at h2
    have htri := dist_triangle (f k z) (Q.ι c'.1) (Q.ι c)
    linarith
  have hVcomp : ∀ k c p z, z ∈ D k →
      dist (Q.ι c) (f k z) < dyadicRadius p / 2 → z ∈ V (k, c, p) := by
    intro k c p z hzD hc
    set y := f k z with hy
    set r : ℝ := dyadicRadius p - dist (Q.ι c) y with hr
    have hr0 : 0 < r := by linarith [dyadicRadius_pos p]
    obtain ⟨m, hm⟩ := Metric.denseRange_iff.mp Q.dense y (r / 4) (by positivity)
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
    have hyc' : y ∈ basicBall Q (m, t) := Metric.mem_ball.mpr (hm.trans ht1)
    obtain ⟨b, hR', hzb⟩ := hRc k z hzD (m, t) hyc'
    refine Set.mem_iUnion₂.mpr ⟨b, ⟨(m, t), hR', ?_⟩, hzb⟩
    change dist (Q.ι m) (Q.ι c) < (((2 ^ p : ℚ)⁻¹ - t : ℚ) : ℝ)
    rw [Rat.cast_sub, cast_inv_two_pow_eq_dyadicRadius]
    have htri := dist_triangle (Q.ι m) y (Q.ι c)
    rw [dist_comm y (Q.ι c)] at htri
    rw [dist_comm] at hm
    linarith
  -- the certified search; the input `w.1` is `(k, p)` and `w.2` the center
  have hU : IsCeOpenFamilyIn P A fun w : (κ × ℕ) × ℕ ↦ O w.1.1 ∪ V (w.1.1, w.2, w.1.2) :=
    (hO.comp (Computable.fst.comp Computable.fst)).union
      (hV.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair (Computable.snd.comp Computable.fst))))
  have hG : IsREIn A fun w : (κ × ℕ) × ℕ ↦ K w.1.1 ⊆ O w.1.1 ∪ V (w.1.1, w.2, w.1.2) :=
    (hK.subset_ceOpen_isREIn hU).comp
      ((Computable.fst.comp Computable.fst).pair Computable.id).computableIn
  obtain ⟨loc, hloc, hdom, hsound⟩ := hG.exists_partrecIn_choice
  refine ⟨loc, hloc, fun k p S hSK hOeq hss hKD z₀ hz₀ ↦ ?_⟩
  have hz₀K : z₀ ∈ K k := hSK hz₀
  have hz₀O : z₀ ∉ O k := fun h ↦ by
    have hmem : z₀ ∈ K k \ S := by
      rw [hOeq]
      exact ⟨hz₀K, h⟩
    exact hmem.2 hz₀
  constructor
  · refine (hdom _).mpr ?_
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp Q.dense (f k z₀) (dyadicRadius p / 2)
      (by linarith [dyadicRadius_pos p])
    refine ⟨c, fun z hz ↦ ?_⟩
    by_cases hzS : z ∈ S
    · have hzz : z = z₀ := hss hzS hz₀
      refine Or.inr ?_
      change z ∈ V (k, c, p)
      rw [hzz]
      exact hVcomp k c p z₀ (hKD hz₀K) (by rw [dist_comm]; exact hc)
    · have hmem : z ∈ K k ∩ O k := by
        rw [← hOeq]
        exact ⟨hz, hzS⟩
      exact Or.inl hmem.2
  · intro q hq
    rcases hsound _ q hq hz₀K with h | h
    · exact (hz₀O h).elim
    · have h' := hVsound k q p z₀ (hKD hz₀K) h
      rw [dist_comm]
      exact h'

/-- A point located by an `A`-partial recursive program along a computable input sequence is
an `A`-computable point: if `loc (g p)` halts for every precision `p` with every output within
`2⁻ᵖ` of `z₀`, then `p ↦ (loc (g p)).get _` is an `A`-computable Cauchy name of `z₀`.
Blueprint node `eff:certified-localization`. -/
theorem certified_localization_point {α : Type*} [Primcodable α] {P : Presentation X}
    {A : Set ℕ} {loc : α →. ℕ} (hloc : PartrecIn {charOracle A} loc) {g : ℕ → α}
    (hg : Computable g) {z₀ : X}
    (h : ∀ p, (loc (g p)).Dom ∧ ∀ q ∈ loc (g p), dist (P.ι q) z₀ < dyadicRadius p) :
    IsComputablePointIn P A z₀ := by
  have hdom : ∀ p, (loc (g p)).Dom := fun p ↦ (h p).1
  refine ⟨fun p ↦ (loc (g p)).get (hdom p), fun p ↦ (h p).2 _ (Part.get_mem (hdom p)), ?_⟩
  exact PartrecIn.of_eq_tot (hloc.comp (hg.computableIn (O := {charOracle A})))
    fun p ↦ Part.get_mem (hdom p)

end Kolmogorov.PointToSet
