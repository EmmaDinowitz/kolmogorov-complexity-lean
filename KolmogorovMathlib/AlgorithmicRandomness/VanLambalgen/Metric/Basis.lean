/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Basis.Radius

/-!
# Existence of almost decidable bases (Hoyrup–Rojas)

A finite measure `μ` on a presented space, computable relative to `A` with total mass computable
relative to `A`, has an almost decidable basis relative to `A` (`exists_isAlmostDecidableBasisIn`).
The basis consists of the balls `B(ι i, r)` with radii `r` in every dyadic interval
`(2^{-(p+1)}, 2^{-p})`, whose spheres are `μ`-null.

The radius is found by a nested-interval search (`exists_nestedRadii`, in
`Metric/Basis/Radius.lean`): rational intervals `(lo n, hi n)`, computable relative to `A`,
strictly nested with widths tending to `0`, whose open annuli about `ι i` have measure at most
`2^{-(n-1)}`. The radius `r` is their common limit. The ball `B(ι i, r)` is the union of the
balls of radii `lo n`, the exterior `{d(·, ι i) > r}` the union of the sets `{d(·, ι i) > hi n}`,
so both are c.e. open relative to `A`; the boundary set, the sphere, lies in every open annulus.
A basic ball `B(ι j, ρ)` is the union of the basis balls `B(ι i, r)` with
`r < 2^{-p}` and a certificate `d(ι i, ι j) < ρ - 2^{-p}`.

## Conventions

The basis is indexed by `Nat.pair i p`, for the centre index `i` and the dyadic level `p` of the
radius. The total mass is computable relative to `A` in the form
`IsComputableRealFamilyIn A fun _ : Unit ↦ μ(X)`.

## Main declarations

* `exists_isAlmostDecidableBasisIn` (blueprint node `vlm:ad-basis-exists`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X}

/-- The limit `⨆ m, lo m` of strictly nested rational intervals with widths tending to `0`
lies strictly inside every interval and is approximated from below by the `lo n` and from above
by the `hi n`. -/
private lemma nested_limit {lo hi : ℕ → ℚ} (hlo : ∀ n, lo n < lo (n + 1))
    (hhi : ∀ n, hi (n + 1) < hi n) (hlh : ∀ n, lo n < hi n)
    (hgap : ∀ n, hi (n + 1) - lo (n + 1) < (2 : ℚ)⁻¹ ^ (n + 1)) :
    (∀ n, (lo n : ℝ) < ⨆ m, (lo m : ℝ) ∧ ⨆ m, (lo m : ℝ) < hi n) ∧
    (∀ d : ℝ, d < ⨆ m, (lo m : ℝ) → ∃ n, d < lo n) ∧
    (∀ d : ℝ, ⨆ m, (lo m : ℝ) < d → ∃ n, (hi n : ℝ) < d) := by
  have hmono : Monotone lo := monotone_nat_of_le_succ fun n ↦ (hlo n).le
  have hanti : Antitone hi := antitone_nat_of_succ_le fun n ↦ (hhi n).le
  have hlohi : ∀ m n, (lo m : ℝ) ≤ hi n := by
    intro m n
    have h : lo m ≤ hi n := (hmono (le_max_left m n)).trans
      ((hlh _).le.trans (hanti (le_max_right m n)))
    exact_mod_cast h
  have hbdd : BddAbove (range fun m ↦ (lo m : ℝ)) := by
    refine ⟨hi 0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact hlohi m 0
  have hle : ∀ n, (lo n : ℝ) ≤ ⨆ m, (lo m : ℝ) := fun n ↦ le_ciSup hbdd n
  have hge : ∀ n, ⨆ m, (lo m : ℝ) ≤ hi n := fun n ↦ ciSup_le fun m ↦ hlohi m n
  refine ⟨fun n ↦ ⟨?_, ?_⟩, fun d hd ↦ exists_lt_of_lt_ciSup hd, fun d hd ↦ ?_⟩
  · exact (show (lo n : ℝ) < lo (n + 1) by exact_mod_cast hlo n).trans_le (hle (n + 1))
  · exact (hge (n + 1)).trans_lt (by exact_mod_cast hhi n)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hd) (show (2 : ℝ)⁻¹ < 1 by norm_num)
    refine ⟨n + 1, ?_⟩
    have h1 : ((hi (n + 1) - lo (n + 1) : ℚ) : ℝ) < (((2 : ℚ)⁻¹ ^ (n + 1) : ℚ) : ℝ) := by
      exact_mod_cast hgap n
    push_cast at h1
    have h2 : (2 : ℝ)⁻¹ ^ (n + 1) ≤ (2 : ℝ)⁻¹ ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
    linarith [hle (n + 1)]

/-- **Hoyrup–Rojas.** A finite Borel measure computable relative to `A`, with total mass computable
relative to `A`, on a presentation whose metric table is computable relative to `A`, has an
almost decidable basis relative to `A`. Blueprint node `vlm:ad-basis-exists`. -/
theorem exists_isAlmostDecidableBasisIn [BorelSpace X] [IsFiniteMeasure μ]
    (hP : ComputablePresentationIn P A) (hμ : IsComputableMeasureIn P A μ)
    (hmass : IsComputableRealFamilyIn A fun _ : Unit => (μ Set.univ).toReal) :
    ∃ B, IsAlmostDecidableBasisIn P A μ B := by
  obtain ⟨lo, hi, hlo, hhi, hspec⟩ := exists_nestedRadii hP hμ hmass
  -- the radii: the limits of the nested intervals
  let r : ℕ × ℕ → ℝ := fun x ↦ ⨆ n, (lo (x, n) : ℝ)
  have hlh : ∀ x n, lo (x, n) < hi (x, n) := by
    intro x n
    cases n with
    | zero =>
      rw [(hspec x).1, (hspec x).2.1]
      exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self _)
    | succ n => exact ((hspec x).2.2 n).2.1
  have hlim := fun x ↦ nested_limit (lo := fun n ↦ lo (x, n)) (hi := fun n ↦ hi (x, n))
    (fun n ↦ ((hspec x).2.2 n).1) (fun n ↦ ((hspec x).2.2 n).2.2.1) (hlh x)
    (fun n ↦ ((hspec x).2.2 n).2.2.2.1)
  have hr1 : ∀ x n, (lo (x, n) : ℝ) < r x ∧ r x < hi (x, n) := fun x n ↦ (hlim x).1 n
  have hr2 : ∀ x (d : ℝ), d < r x → ∃ n, d < lo (x, n) := fun x ↦ (hlim x).2.1
  have hr3 : ∀ x (d : ℝ), r x < d → ∃ n, (hi (x, n) : ℝ) < d := fun x ↦ (hlim x).2.2
  have hrad : ∀ x, dyadicRadius (x.2 + 1) < r x ∧ r x < dyadicRadius x.2 := by
    intro x
    rw [← cast_inv_two_pow, ← cast_inv_two_pow, ← (hspec x).1, ← (hspec x).2.1]
    exact hr1 x 0
  -- the members, exteriors and boundary covers, indexed by `(i, p)`
  have hn : ∀ i, IsCauchyName P (P.ι i) fun _ ↦ i := isCauchyName_const P
  have hc : ComputableIn {charOracle A} fun ip : ℕ × ℕ ↦ ip.1 := ComputableIn.fst
  have hball := isCeOpenFamilyIn_dist_lt hP hn hc
  have hext := isCeOpenFamilyIn_lt_dist hP hn hc
  have hBx : IsCeOpenFamilyIn P A fun x : ℕ × ℕ ↦ Metric.ball (P.ι x.1) (r x) := by
    have h := (hball.compIn (g := fun v : (ℕ × ℕ) × ℕ ↦ (v.1.1, lo v))
      ((ComputableIn.fst.comp ComputableIn.fst).pair hlo)).iUnion
    have heq : (fun x : ℕ × ℕ ↦ Metric.ball (P.ι x.1) (r x)) =
        fun x ↦ ⋃ n, {y | dist y (P.ι x.1) < (lo (x, n) : ℝ)} := by
      funext x
      ext y
      simp only [Metric.mem_ball, mem_iUnion, mem_ofPred_eq]
      constructor
      · exact hr2 x _
      · rintro ⟨n, hn⟩
        exact hn.trans (hr1 x n).1
    rw [heq]
    exact h
  have hDx : IsCeOpenFamilyIn P A fun x : ℕ × ℕ ↦ {y | r x < dist y (P.ι x.1)} := by
    have h := (hext.compIn (g := fun v : (ℕ × ℕ) × ℕ ↦ (v.1.1, hi v))
      ((ComputableIn.fst.comp ComputableIn.fst).pair hhi)).iUnion
    have heq : (fun x : ℕ × ℕ ↦ {y | r x < dist y (P.ι x.1)}) =
        fun x ↦ ⋃ n, {y | (hi (x, n) : ℝ) < dist y (P.ι x.1)} := by
      funext x
      ext y
      simp only [mem_iUnion, mem_ofPred_eq]
      constructor
      · exact hr3 x _
      · rintro ⟨n, hn⟩
        exact (hr1 x n).2.trans hn
    rw [heq]
    exact h
  have hWx : IsCeOpenFamilyIn P A fun v : (ℕ × ℕ) × ℕ ↦
      {y | (lo (v.1, v.2 + 1) : ℝ) < dist y (P.ι v.1.1)} ∩
        {y | dist y (P.ι v.1.1) < (hi (v.1, v.2 + 1) : ℝ)} := by
    have hsucc : ComputableIn {charOracle A} fun v : (ℕ × ℕ) × ℕ ↦ (v.1, v.2 + 1) :=
      ComputableIn.fst.pair (Computable.succ.computableIn.comp ComputableIn.snd)
    exact IsCeOpenFamilyIn.inter P A hP
      (hext.compIn (g := fun v : (ℕ × ℕ) × ℕ ↦ (v.1.1, lo (v.1, v.2 + 1)))
        ((ComputableIn.fst.comp ComputableIn.fst).pair (hlo.comp hsucc)))
      (hball.compIn (g := fun v : (ℕ × ℕ) × ℕ ↦ (v.1.1, hi (v.1, v.2 + 1)))
        ((ComputableIn.fst.comp ComputableIn.fst).pair (hhi.comp hsucc)))
  have hunpair : Computable Nat.unpair := Primrec.unpair.to_comp
  refine ⟨fun k ↦ Metric.ball (P.ι (Nat.unpair k).1) (r (Nat.unpair k)),
    ⟨hBx.comp hunpair, ?_, ?_⟩⟩
  · -- exteriors and boundary covers
    refine ⟨fun k ↦ {y | r (Nat.unpair k) < dist y (P.ι (Nat.unpair k).1)},
      fun kn ↦ {y | (lo (Nat.unpair kn.1, kn.2 + 1) : ℝ) < dist y (P.ι (Nat.unpair kn.1).1)} ∩
        {y | dist y (P.ι (Nat.unpair kn.1).1) < (hi (Nat.unpair kn.1, kn.2 + 1) : ℝ)},
      hDx.comp hunpair, hWx.comp ((hunpair.comp Computable.fst).pair Computable.snd),
      fun k ↦ ⟨?_, fun n ↦ ⟨?_, ?_⟩⟩⟩
    · exact Set.disjoint_left.mpr fun y h1 h2 ↦ lt_asymm (Metric.mem_ball.mp h1) h2
    · intro y hy
      simp only [mem_compl_iff, mem_union, Metric.mem_ball, mem_ofPred_eq, not_or,
        not_lt] at hy
      have hd : dist y (P.ι (Nat.unpair k).1) = r (Nat.unpair k) := le_antisymm hy.2 hy.1
      refine ⟨?_, ?_⟩
      · change (lo (Nat.unpair k, n + 1) : ℝ) < dist y (P.ι (Nat.unpair k).1)
        rw [hd]
        exact (hr1 _ _).1
      · change dist y (P.ι (Nat.unpair k).1) < (hi (Nat.unpair k, n + 1) : ℝ)
        rw [hd]
        exact (hr1 _ _).2
    · exact ((hspec (Nat.unpair k)).2.2 n).2.2.2.2
  · -- generation of the basic balls
    let E : (ℕ × ℚ) × List ℕ → Prop := fun w ↦ ∃ x : ℕ × ℕ, w.2 = [Nat.pair x.1 x.2] ∧
      dist (P.ι x.1) (P.ι w.1.1) < ((w.1.2 - (2 : ℚ)⁻¹ ^ x.2 : ℚ) : ℝ)
    have hE : IsREIn A E := by
      have h1 : IsREIn A fun v : ((ℕ × ℚ) × List ℕ) × (ℕ × ℕ) ↦
          v.1.2 = [Nat.pair v.2.1 v.2.2] :=
        isREIn_of_computable_decide (Primrec.eq.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.snd.comp Primrec.snd)) (Primrec.const []))).decide.to_comp
      have h2 : IsREIn A fun v : ((ℕ × ℚ) × List ℕ) × (ℕ × ℕ) ↦
          dist (P.ι v.2.1) (P.ι v.1.1.1) < ((v.1.1.2 - (2 : ℚ)⁻¹ ^ v.2.2 : ℚ) : ℝ) :=
        (birkhoff_computableIn_lt A _ hP).comp (((Computable.fst.comp Computable.snd).pair
          (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
          (computable₂_ratSub.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
            (computable_inv_two_pow.comp (Computable.snd.comp Computable.snd)))).computableIn
      exact (h1.and h2).exists
    refine ⟨E, hE, fun b ↦ ?_⟩
    ext y
    constructor
    · intro hy
      have hy' : dist y (P.ι b.1) < b.2 := Metric.mem_ball.mp hy
      obtain ⟨p, hp⟩ := exists_dyadicRadius_lt
        (show 0 < ((b.2 : ℝ) - dist y (P.ι b.1)) / 2 by linarith)
      obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.dense y (dyadicRadius (p + 1))
        (dyadicRadius_pos _)
      have hpp : dyadicRadius (p + 1) ≤ dyadicRadius p := dyadicRadius_antitone (Nat.le_succ p)
      refine mem_iUnion₂.mpr ⟨[Nat.pair i p], ⟨(i, p), rfl, ?_⟩, ?_⟩
      · have htri := dist_triangle (P.ι i) y (P.ι b.1)
        rw [dist_comm (P.ι i) y] at htri
        change dist (P.ι i) (P.ι b.1) < ((b.2 - (2 : ℚ)⁻¹ ^ p : ℚ) : ℝ)
        rw [Rat.cast_sub, cast_inv_two_pow]
        linarith
      · simp only [List.mem_singleton, iInter_iInter_eq_left, Nat.unpair_pair]
        exact Metric.mem_ball.mpr (hi.trans (hrad (i, p)).1)
    · intro hy
      obtain ⟨L, ⟨x, hL, hcert⟩, hyL⟩ := mem_iUnion₂.mp hy
      change L = [Nat.pair x.1 x.2] at hL
      subst hL
      simp only [List.mem_singleton, iInter_iInter_eq_left, Nat.unpair_pair] at hyL
      have hyx : dist y (P.ι x.1) < r (x.1, x.2) := Metric.mem_ball.mp hyL
      have hcert' : dist (P.ι x.1) (P.ι b.1) < ((b.2 - (2 : ℚ)⁻¹ ^ x.2 : ℚ) : ℝ) := hcert
      rw [Rat.cast_sub, cast_inv_two_pow] at hcert'
      have htri := dist_triangle y (P.ι x.1) (P.ι b.1)
      have hrx := (hrad (x.1, x.2)).2
      exact Metric.mem_ball.mpr (by linarith)

end Kolmogorov.PointToSet
