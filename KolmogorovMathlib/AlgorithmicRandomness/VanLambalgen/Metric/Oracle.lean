/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.Oracle.Joins
import KolmogorovMathlib.Oracle.Search
import KolmogorovMathlib.PointToSet.ComputableMetric.Points

/-!
# The itinerary as an oracle for a point

For an almost decidable basis `B` relative to `A`, the itinerary of a point and its Cauchy names
compute each other relative to `A`:

* the itinerary computes a name, for every point (`exists_isCauchyName_le_itinerary`): search for
  a small basic ball written as a finite intersection of members containing the point;
* every name computes the itinerary at a random point (`itinerary_le_of_mem_randomPoints`): a
  random point lies in no boundary set `(B k ∪ D k)ᶜ`, so bit `k` is found by searching for a
  certificate of `x ∈ B k` or of `x ∈ D k`.

So at a random point, `A ⊕ itinerary` is the least of the degrees `A ⊕ a` over the names `a`.

## Conventions

Names are encoded by their graphs (`nameOracle`); oracles are joined with
`PointToSet.oracleJoin`.

## Main declarations

* `computableIn_nameOracle_oracleJoin`, `charOracle_nameOracle_le` (blueprint node
  `vlm:oracle`): a function is computable relative to `A` joined with its graph, and the graph
  of a relatively computable function is reducible to the oracle; also used by
  `Metric/Countable/Presentation.lean`.

* `IsAlmostDecidableBasisIn.exists_isCauchyName_le_itinerary`,
  `IsAlmostDecidableBasisIn.itinerary_le_of_mem_randomPoints` (blueprint node `vlm:oracle`).

Used by `AlgorithmicRandomness/VanLambalgen/Metric/MainResults.lean`.
-/

namespace Kolmogorov.PointToSet

open MeasureTheory
open scoped Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {P : Presentation X} {A : Set ℕ}
  {μ : Measure X} {B : ℕ → Set X}

/-! ### Oracle bookkeeping -/

/-- A set whose membership is decided by a Boolean function computable relative to `J` is
Turing reducible to `J`. -/
private lemma charOracle_le_of_computableIn {S J : Set ℕ} {c : ℕ → Bool}
    (hc : ComputableIn {charOracle J} c) (hS : ∀ n, n ∈ S ↔ c n = true) :
    charOracle S ≤ᵀ charOracle J := by
  have h : ComputableIn {charOracle J} fun n ↦ cond (c n) 1 0 :=
    computable_in_cond hc (ComputableIn.const 1) (ComputableIn.const 0)
  refine PartrecIn.of_eq h fun n ↦ ?_
  classical
  by_cases hn : c n = true
  · simp [charOracle, (hS n).mpr hn, hn]
  · have hn' : c n = false := by simpa using hn
    have hS' : n ∉ S := fun h ↦ hn ((hS n).mp h)
    simp [charOracle, hS', hn']

/-- The second component of a join is readable bit by bit: a sequence is computable relative to
`A ⊕ u`. -/
private lemma computableIn_seq_oracleJoin (A : Set ℕ) (u : CantorSeq) :
    ComputableIn {charOracle (oracleJoin A (seqOracle u))} u := by
  set J := oracleJoin A (seqOracle u)
  have hq : PartrecIn {charOracle J} fun n : ℕ ↦ charOracle J (2 * n + 1) :=
    PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
        (Primrec.const 1)).computableIn
  have ht : ComputableIn₂ {charOracle J} fun (_ : ℕ) (r : ℕ) ↦ decide (r = 1) :=
    (PrimrecPred.decide
      (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 1))).to₂.to_comp.computableIn₂
  refine PartrecIn.of_eq_tot (hq.map ht) fun n ↦ ?_
  classical
  have hodd : (2 * n + 1) % 2 = 1 := by omega
  have hodd' : (2 * n + 1) / 2 = n := by omega
  cases hun : u n
  · simp [J, charOracle, oracleJoin, seqOracle, hodd, hodd', hun]
  · simp [J, charOracle, oracleJoin, seqOracle, hodd, hodd', hun]

/-- A function is computable relative to `A` joined with its graph: search the graph.
Blueprint node `vlm:oracle`. -/
theorem computableIn_nameOracle_oracleJoin (A : Set ℕ) (a : ℕ → ℕ) :
    ComputableIn {charOracle (oracleJoin A (nameOracle a))} a := by
  set K := oracleJoin A (nameOracle a)
  have hquery : PartrecIn {charOracle K}
      fun q : ℕ × ℕ ↦ charOracle K (2 * Nat.pair q.1 q.2 + 1) :=
    PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp Primrec.fst Primrec.snd)) (Primrec.const 1)).computableIn
  have htest : ComputableIn₂ {charOracle K} fun (_ : ℕ × ℕ) (r : ℕ) ↦ decide (r = 1) :=
    (PrimrecPred.decide
      (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 1))).to₂.to_comp.computableIn₂
  have hsearch := PartrecIn.rfind (hquery.map htest).to₂
  refine PartrecIn.of_eq_tot hsearch fun p ↦ ?_
  classical
  have hmem : ∀ m, 2 * Nat.pair p m + 1 ∈ K ↔ a p = m := by
    intro m
    have hodd : (2 * Nat.pair p m + 1) % 2 = 1 := by omega
    have hodd' : (2 * Nat.pair p m + 1) / 2 = Nat.pair p m := by omega
    simp [K, oracleJoin, nameOracle, hodd, hodd', Nat.unpair_pair]
  refine Nat.mem_rfind.mpr ⟨?_, fun {m} hm ↦ ?_⟩
  · simp [charOracle, (hmem (a p)).mpr rfl]
  · have hne : a p ≠ m := Nat.ne_of_gt hm
    have hK : 2 * Nat.pair p m + 1 ∉ K := fun h ↦ hne ((hmem m).mp h)
    simp [charOracle, hK]

/-- The graph of a total function computable relative to `J` is Turing reducible to `J`.
Blueprint node `vlm:oracle`. -/
theorem charOracle_nameOracle_le {J : Set ℕ} {a : ℕ → ℕ}
    (ha : ComputableIn {charOracle J} a) : charOracle (nameOracle a) ≤ᵀ charOracle J := by
  have h1 : ComputableIn {charOracle J} fun n : ℕ ↦ a (Nat.unpair n).1 :=
    ha.comp (Primrec.fst.comp Primrec.unpair).computableIn
  have h2 : ComputableIn {charOracle J} fun n : ℕ ↦ (Nat.unpair n).2 :=
    (Primrec.snd.comp Primrec.unpair).computableIn
  have h := ComputableIn₂.comp (Primrec.eq.decide.computableIn₂ (O := {charOracle J})) h1 h2
  exact charOracle_le_of_computableIn h fun n ↦ by simp [nameOracle]

omit [MeasurableSpace X] in
/-- Membership of a fixed point in the members of a c.e. open family is relatively enumerable
once membership in basic balls is. -/
private lemma isREIn_mem_of_isCeOpenFamilyIn {K : Set ℕ} {U : ℕ → Set X} {x : X}
    (hU : IsCeOpenFamilyIn P K U) (hball : IsREIn K fun b : ℕ × ℚ ↦ x ∈ basicBall P b) :
    IsREIn K fun k ↦ x ∈ U k := by
  obtain ⟨E, hE, hUE⟩ := hU
  have h := IsREIn.exists (F := fun w : ℕ × (ℕ × ℚ) ↦ E w ∧ x ∈ basicBall P w.2)
    (hE.and (hball.comp ComputableIn.snd))
  have heq : (fun k ↦ x ∈ U k) = fun k ↦ ∃ b : ℕ × ℚ, E (k, b) ∧ x ∈ basicBall P b := by
    funext k
    rw [hUE k]
    simp
  rw [heq]
  exact h

omit [MetricSpace X] [MeasurableSpace X] in
/-- Bit `k` of the itinerary is `true` exactly when the point lies in `B k`. -/
private lemma itinerary_eq_true_iff {x : X} {k : ℕ} : itinerary B x k = true ↔ x ∈ B k := by
  simp [itinerary]

/-! ### The itinerary computes a name -/

/-- The itinerary of a point in an almost decidable basis computes, relative to `A`, a Cauchy name
of the point. Blueprint node `vlm:oracle`. -/
theorem IsAlmostDecidableBasisIn.exists_isCauchyName_le_itinerary
    (hB : IsAlmostDecidableBasisIn P A μ B) (x : X) :
    ∃ a, IsCauchyName P x a ∧
      charOracle (oracleJoin A (nameOracle a)) ≤ᵀ
        charOracle (oracleJoin A (seqOracle (itinerary B x))) := by
  set J := oracleJoin A (seqOracle (itinerary B x))
  have hAJ : charOracle A ≤ᵀ charOracle J := oracle_joins A _
  obtain ⟨E, hE, hgen⟩ := hB.generates
  -- the search: a code `((m, q), L)` of a ball of radius `< 2⁻ᵖ` that is listed by `E` and
  -- whose intersection `⋂ k ∈ L, B k` contains `x` according to the itinerary
  let G : ℕ × ((ℕ × ℚ) × List ℕ) → Prop := fun w ↦
    E w.2 ∧ w.2.1.2 < (2 ^ w.1 : ℚ)⁻¹ ∧
      ∀ k : ℕ, ∀ h : k < w.2.2.length, itinerary B x (w.2.2.get ⟨k, h⟩) = true
  have hbit : IsREIn J fun k : ℕ ↦ itinerary B x k = true :=
    isREIn_of_computableIn_decide J _
      ((computableIn_seq_oracleJoin A (itinerary B x)).of_eq fun k ↦ by simp)
  have hG : IsREIn J G := by
    have h1 : IsREIn J fun w : ℕ × ((ℕ × ℚ) × List ℕ) ↦ E w.2 :=
      (hE.mono_oracle hAJ).comp ComputableIn.snd
    have h2 : IsREIn J fun w : ℕ × ((ℕ × ℚ) × List ℕ) ↦ w.2.1.2 < (2 ^ w.1 : ℚ)⁻¹ :=
      isREIn_of_computable_decide (computable₂_ratLt.comp
        (Computable.snd.comp (Computable.fst.comp Computable.snd))
        (computable_rat_inv_two_pow.comp Computable.fst))
    have h3 := (IsREIn.list_forall_get (α := Unit)
      (F := fun d : Unit × ℕ × ℕ ↦ itinerary B x d.2.2 = true)
      (hbit.comp (ComputableIn.snd.comp ComputableIn.snd))).comp
      (f := fun w : ℕ × ((ℕ × ℚ) × List ℕ) ↦ ((), w.2.2))
      ((ComputableIn.const ()).pair (ComputableIn.snd.comp ComputableIn.snd))
    exact h1.and (h2.and h3)
  have htot : ∀ p, ∃ w, G (p, w) := by
    intro p
    obtain ⟨c, hxc, -, hc⟩ := exists_mem_basicBall_radius_lt P x p
    rw [hgen c] at hxc
    obtain ⟨L, hL, hxL⟩ := Set.mem_iUnion₂.mp hxc
    refine ⟨(c, L), hL, hc, fun k hk ↦ ?_⟩
    exact itinerary_eq_true_iff.mpr (Set.mem_iInter₂.mp hxL _ (List.get_mem L ⟨k, hk⟩))
  obtain ⟨g, hg, hgG⟩ := hG.exists_computableIn_choice htot
  refine ⟨fun p ↦ (g p).1.1, fun p ↦ ?_, ?_⟩
  · obtain ⟨hEg, hlt, hL⟩ := hgG p
    have hx : x ∈ basicBall P (g p).1 := by
      rw [hgen]
      refine Set.mem_iUnion₂.mpr ⟨(g p).2, hEg, Set.mem_iInter₂.mpr fun k hk ↦ ?_⟩
      obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_iff_get.mp hk
      exact itinerary_eq_true_iff.mp (hL i hi)
    have hd : dist x (P.ι (g p).1.1) < ((g p).1.2 : ℝ) := Metric.mem_ball.mp hx
    have hlt' : (((g p).1.2 : ℚ) : ℝ) < (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) := Rat.cast_lt.mpr hlt
    have hr : (((2 ^ p : ℚ)⁻¹ : ℚ) : ℝ) = dyadicRadius p := by
      simp [dyadicRadius, inv_pow]
    rw [dist_comm]
    rw [hr] at hlt'
    exact hd.trans hlt'
  · refine oracle_joins_least A _ J hAJ (charOracle_nameOracle_le ?_)
    exact (ComputableIn.fst.comp (ComputableIn.fst.comp hg)).of_eq fun _ ↦ rfl

/-! ### A name computes the itinerary at a random point -/

/-- At a point that is `μ`-random relative to `A`, every Cauchy name computes the itinerary
relative to `A`, provided the presentation has a metric table computable relative to `A`.
Blueprint node `vlm:oracle`. -/
theorem IsAlmostDecidableBasisIn.itinerary_le_of_mem_randomPoints
    (hB : IsAlmostDecidableBasisIn P A μ B) (hP : ComputablePresentationIn P A) {x : X}
    (hx : x ∈ randomPoints P A μ) {a : ℕ → ℕ} (ha : IsCauchyName P x a) :
    charOracle (oracleJoin A (seqOracle (itinerary B x))) ≤ᵀ
      charOracle (oracleJoin A (nameOracle a)) := by
  set K := oracleJoin A (nameOracle a)
  have hAK : charOracle A ≤ᵀ charOracle K := oracle_joins A _
  obtain ⟨D, W, hD, hW, hBD⟩ := hB.exists_exterior
  -- the point lies in `B k` or in `D k`, since it is not in the null boundary set
  have hcover : ∀ k, x ∈ B k ∨ x ∈ D k := by
    intro k
    have hWk : IsCeOpenFamilyIn P A fun n ↦ W (k, n) :=
      hW.comp (g := fun n : ℕ ↦ (k, n)) ((Computable.const k).pair Computable.id)
    obtain ⟨m, hm⟩ := not_forall_mem_of_mem_randomPoints hx hWk (c := 0)
      fun m ↦ by simpa using ((hBD k).2 m).2
    by_contra hk
    exact hm (((hBD k).2 m).1 (by simpa [not_or] using hk))
  -- semidecision procedures for `x ∈ B k` and `x ∈ D k`
  have hacomp : ComputableIn {charOracle K} a := computableIn_nameOracle_oracleJoin A a
  have hball : IsREIn K fun b : ℕ × ℚ ↦ x ∈ basicBall P b :=
    isREIn_mem_basicBall_of_name (isComputableRealFamilyIn_mono_oracle hP hAK) ha hacomp
  have hBK : IsREIn K fun k ↦ x ∈ B k :=
    isREIn_mem_of_isCeOpenFamilyIn (isCeOpenFamilyIn_mono (P := P) (A := A) hAK
      hB.isCeOpenFamilyIn) hball
  have hDK : IsREIn K fun k ↦ x ∈ D k :=
    isREIn_mem_of_isCeOpenFamilyIn (isCeOpenFamilyIn_mono (P := P) (A := A) hAK hD) hball
  let G : ℕ × Bool → Prop := fun w ↦ (w.2 = true ∧ x ∈ B w.1) ∨ (w.2 = false ∧ x ∈ D w.1)
  have hG : IsREIn K G := by
    have ht : IsREIn K fun w : ℕ × Bool ↦ w.2 = true :=
      isREIn_of_computable_decide (Primrec.eq.decide.comp Primrec.snd (Primrec.const true)).to_comp
    have hf : IsREIn K fun w : ℕ × Bool ↦ w.2 = false :=
      isREIn_of_computable_decide
        (Primrec.eq.decide.comp Primrec.snd (Primrec.const false)).to_comp
    exact (ht.and (hBK.comp ComputableIn.fst)).or (hf.and (hDK.comp ComputableIn.fst))
  have htot : ∀ k, ∃ b, G (k, b) := by
    intro k
    rcases hcover k with h | h
    · exact ⟨true, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨false, Or.inr ⟨rfl, h⟩⟩
  obtain ⟨g, hg, hgG⟩ := hG.exists_computableIn_choice htot
  have hgit : ∀ k, g k = true ↔ k ∈ seqOracle (itinerary B x) := by
    intro k
    change g k = true ↔ itinerary B x k = true
    rw [itinerary_eq_true_iff]
    rcases hgG k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact iff_of_true h1 h2
    · have h1' : g k = false := h1
      refine iff_of_false (by simp [h1']) fun hBk ↦ ?_
      exact Set.disjoint_left.mp (hBD k).1 hBk h2
  exact oracle_joins_least A _ K hAK
    (charOracle_le_of_computableIn hg fun n ↦ (hgit n).symm)

end Kolmogorov.PointToSet
