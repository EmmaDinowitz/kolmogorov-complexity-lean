/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.Points

/-!
# Relatively c.e. open sets and families

A set is relatively c.e. open when it is the union of an enumerable set of basic balls
(`IsCeOpenIn`); a family indexed by a primcodable type is c.e. open uniformly in the index
(`IsCeOpenFamilyIn`). Such families are closed under reindexing along computable maps, finite
and countable unions, restriction by a decidable condition, unions over the members of a list
and, above an oracle computing the metric table, finite intersections
(`IsCeOpenFamilyIn.inter`). Balls about points with uniformly computable names and the
complements of their closed balls are c.e. open uniformly in the radius, every open set is the
union of the basic balls it contains, and an open set containing `z` contains a coded basic
ball `basicBall P (c, rV)` around `z` (`exists_basicBall_code`). The finite unions `ballUnion`
of coded basic balls form a c.e. open family in the list of codes.
Blueprint node `eff:ce-open`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A set is relatively c.e. open when it is the union of an enumerable set of basic balls.
Blueprint node `geo:effective-data`. -/
def IsCeOpenIn (P : Presentation X) (A : Set ℕ) (U : Set X) : Prop :=
  ∃ E : ℕ × ℚ → Prop, IsREIn A E ∧ U = ⋃ b ∈ {b | E b}, basicBall P b

/-- A family of sets indexed by a primcodable type, c.e. open uniformly in the index.
Blueprint node `geo:effective-data` (item 5). -/
def IsCeOpenFamilyIn {ι : Type*} [Primcodable ι] (P : Presentation X) (A : Set ℕ)
    (U : ι → Set X) : Prop :=
  ∃ E : ι × (ℕ × ℚ) → Prop, IsREIn A E ∧ ∀ i, U i = ⋃ b ∈ {b | E (i, b)}, basicBall P b

section aux

variable {P : Presentation X} {Q : Presentation Y} {A B : Set ℕ}

/-- Reindexing a c.e. open family along a computable map of indices. -/
theorem IsCeOpenFamilyIn.comp {ι κ : Type*} [Primcodable ι] [Primcodable κ] {U : ι → Set X}
    (hU : IsCeOpenFamilyIn P A U) {g : κ → ι} (hg : Computable g) :
    IsCeOpenFamilyIn P A fun k ↦ U (g k) := by
  obtain ⟨E, hE, hU⟩ := hU
  exact ⟨fun kb ↦ E (g kb.1, kb.2),
    hE.comp ((hg.comp Computable.fst).pair Computable.snd).computableIn, fun k ↦ hU (g k)⟩

/-- Finite unions of c.e. open families are c.e. open, uniformly (no metric table needed). -/
theorem IsCeOpenFamilyIn.union {ι : Type*} [Primcodable ι] {U V : ι → Set X}
    (hU : IsCeOpenFamilyIn P A U) (hV : IsCeOpenFamilyIn P A V) :
    IsCeOpenFamilyIn P A fun i ↦ U i ∪ V i := by
  obtain ⟨E, hE, hU⟩ := hU
  obtain ⟨E', hE', hV⟩ := hV
  refine ⟨fun ib ↦ E ib ∨ E' ib, hE.or hE', fun i ↦ ?_⟩
  ext y
  rw [Set.mem_union, hU i, hV i]
  constructor
  · rintro (hy | hy)
    · obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨b, Or.inl hb, hyb⟩
    · obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨b, Or.inr hb, hyb⟩
  · intro hy
    obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
    rcases hb with hb | hb
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨b, hb, hyb⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨b, hb, hyb⟩)

/-- Countable unions along a primcodable index of a c.e. open family are c.e. open,
uniformly in the remaining index. -/
theorem IsCeOpenFamilyIn.iUnion {ι κ : Type*} [Primcodable ι] [Primcodable κ]
    {U : ι × κ → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsCeOpenFamilyIn P A fun i ↦ ⋃ k, U (i, k) := by
  obtain ⟨E, hE, hU⟩ := hU
  refine ⟨fun ib ↦ ∃ k, E ((ib.1, k), ib.2), ?_, fun i ↦ ?_⟩
  · exact (hE.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst)).computableIn).exists
  · ext y
    constructor
    · intro hy
      obtain ⟨k, hy⟩ := Set.mem_iUnion.mp hy
      rw [hU (i, k)] at hy
      obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨b, ⟨k, hb⟩, hyb⟩
    · intro hy
      obtain ⟨b, ⟨k, hb⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      rw [hU (i, k)]
      exact Set.mem_iUnion₂.mpr ⟨b, hb, hyb⟩

/-- Restricting a c.e. open family by a computably decidable condition on the index (the set
is emptied where the condition fails) keeps it c.e. open. -/
theorem IsCeOpenFamilyIn.ite {ι : Type*} [Primcodable ι] {U : ι → Set X}
    (hU : IsCeOpenFamilyIn P A U) {p : ι → Prop} [DecidablePred p]
    (hp : Computable fun i ↦ decide (p i)) :
    IsCeOpenFamilyIn P A fun i ↦ if p i then U i else ∅ := by
  obtain ⟨E, hE, hU⟩ := hU
  refine ⟨fun ib ↦ p ib.1 ∧ E ib,
    (isREIn_of_computable_decide (hp.comp Computable.fst)).and hE, fun i ↦ ?_⟩
  change (if p i then U i else ∅) = ⋃ b ∈ {b | p i ∧ E (i, b)}, basicBall P b
  by_cases hi : p i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hi), hU i]
    ext y
    constructor
    · intro hy
      obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨b, ⟨hi, hb⟩, hyb⟩
    · intro hy
      obtain ⟨b, ⟨_, hb⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr ⟨b, hb, hyb⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)]
    ext y
    constructor
    · intro hy
      exact hy.elim
    · intro hy
      obtain ⟨b, ⟨hb, _⟩, _⟩ := Set.mem_iUnion₂.mp hy
      exact (hi hb).elim

/-- The sets `{w | ρ < dist w w₀}`, for points `w₀` with uniformly computable names, form a c.e.
open family in `(index, ρ)`: a basic ball is listed when a rational certificate
`ρ + radius < dist w₀ center` holds. -/
theorem isCeOpenFamilyIn_lt_dist {κ : Type*} [Primcodable κ] (hP : ComputablePresentationIn P A)
    {w₀ : κ → X} {a : κ → ℕ → ℕ} (ha : ∀ k, IsCauchyName P (w₀ k) (a k))
    (hcomp : ComputableIn {charOracle A} fun kp : κ × ℕ ↦ a kp.1 kp.2) :
    IsCeOpenFamilyIn P A fun d : κ × ℚ ↦ {w | (d.2 : ℝ) < dist w (w₀ d.1)} := by
  have hlt := isREIn_rat_lt_dist_names hP ha hcomp
  refine ⟨fun db ↦ (0 : ℚ) < db.2.2 ∧ ((db.1.2 + db.2.2 : ℚ) : ℝ) < dist (w₀ db.1.1) (P.ι db.2.1),
    ?_, fun d ↦ ?_⟩
  · have hre : ComputableIn {charOracle A} fun db : (κ × ℚ) × (ℕ × ℚ) ↦
        ((db.1.1, db.2.1), db.1.2 + db.2.2) :=
      (((Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)).pair
        (computable₂_ratAdd.comp (Computable.snd.comp Computable.fst)
          (Computable.snd.comp Computable.snd))).computableIn
    exact (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp Computable.snd))).and (hlt.comp hre)
  · ext y
    constructor
    · intro hy
      have hy' : (d.2 : ℝ) < dist y (w₀ d.1) := hy
      set r : ℝ := dist y (w₀ d.1) - d.2 with hr
      have hr0 : 0 < r := by linarith
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense y (r / 4) (by positivity)
      obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
      have htri := dist_triangle (w₀ d.1) (P.ι k) y
      rw [dist_comm (w₀ d.1) y, dist_comm (P.ι k) y] at htri
      refine Set.mem_iUnion₂.mpr ⟨(k, t), ⟨?_, ?_⟩, Metric.mem_ball.mpr (hk.trans ht1)⟩
      · exact_mod_cast (show (0 : ℝ) < r / 4 by positivity).trans ht1
      · change ((d.2 + t : ℚ) : ℝ) < dist (w₀ d.1) (P.ι k)
        push_cast
        linarith
    · intro hy
      obtain ⟨b, ⟨_, hb⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
      have hyb' : dist y (P.ι b.1) < b.2 := hyb
      have hb' : (d.2 : ℝ) + b.2 < dist (w₀ d.1) (P.ι b.1) := by
        have h : ((d.2 + b.2 : ℚ) : ℝ) < dist (w₀ d.1) (P.ι b.1) := hb
        push_cast at h
        exact h
      change (d.2 : ℝ) < dist y (w₀ d.1)
      have htri := dist_triangle (w₀ d.1) y (P.ι b.1)
      rw [dist_comm (w₀ d.1) y] at htri
      linarith

/-- The open balls about points with uniformly computable names, with rational radii, form a
c.e. open family in `(index, radius)`: a basic ball is listed when a rational certificate
`dist w₀ center + radius < h` holds. -/
theorem isCeOpenFamilyIn_dist_lt {κ : Type*} [Primcodable κ] (hP : ComputablePresentationIn P A)
    {w₀ : κ → X} {a : κ → ℕ → ℕ} (ha : ∀ k, IsCauchyName P (w₀ k) (a k))
    (hcomp : ComputableIn {charOracle A} fun kp : κ × ℕ ↦ a kp.1 kp.2) :
    IsCeOpenFamilyIn P A fun d : κ × ℚ ↦ {w | dist w (w₀ d.1) < (d.2 : ℝ)} := by
  have hlt := birkhoff_computableIn_lt A _ (isComputableRealFamilyIn_dist_names hP ha hcomp)
  refine ⟨fun db ↦ (0 : ℚ) < db.2.2 ∧ dist (w₀ db.1.1) (P.ι db.2.1) < ((db.1.2 - db.2.2 : ℚ) : ℝ),
    ?_, fun d ↦ ?_⟩
  · have hre : ComputableIn {charOracle A} fun db : (κ × ℚ) × (ℕ × ℚ) ↦
        ((db.1.1, db.2.1), db.1.2 - db.2.2) :=
      (((Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)).pair
        (computable₂_ratSub.comp (Computable.snd.comp Computable.fst)
          (Computable.snd.comp Computable.snd))).computableIn
    exact (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp Computable.snd))).and (hlt.comp hre)
  · ext y
    constructor
    · intro hy
      have hy' : dist y (w₀ d.1) < (d.2 : ℝ) := hy
      set r : ℝ := d.2 - dist y (w₀ d.1) with hr
      have hr0 : 0 < r := by linarith
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense y (r / 4) (by positivity)
      obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
      have htri := dist_triangle (w₀ d.1) y (P.ι k)
      rw [dist_comm (w₀ d.1) y] at htri
      refine Set.mem_iUnion₂.mpr ⟨(k, t), ⟨?_, ?_⟩, Metric.mem_ball.mpr (hk.trans ht1)⟩
      · exact_mod_cast (show (0 : ℝ) < r / 4 by positivity).trans ht1
      · change dist (w₀ d.1) (P.ι k) < ((d.2 - t : ℚ) : ℝ)
        push_cast
        linarith
    · intro hy
      obtain ⟨b, ⟨_, hb⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
      have hyb' : dist y (P.ι b.1) < b.2 := hyb
      have hb' : dist (w₀ d.1) (P.ι b.1) < (d.2 : ℝ) - b.2 := by
        have h : dist (w₀ d.1) (P.ι b.1) < ((d.2 - b.2 : ℚ) : ℝ) := hb
        push_cast at h
        exact h
      change dist y (w₀ d.1) < (d.2 : ℝ)
      have htri := dist_triangle y (P.ι b.1) (w₀ d.1)
      rw [dist_comm (P.ι b.1) (w₀ d.1)] at htri
      linarith

/-- Reindexing a c.e. open family along an oracle-computable map of indices. -/
theorem IsCeOpenFamilyIn.compIn {ι κ : Type*} [Primcodable ι] [Primcodable κ] {U : ι → Set X}
    (hU : IsCeOpenFamilyIn P A U) {g : κ → ι} (hg : ComputableIn {charOracle A} g) :
    IsCeOpenFamilyIn P A fun k ↦ U (g k) := by
  obtain ⟨E, hE, hU⟩ := hU
  exact ⟨fun kb ↦ E (g kb.1, kb.2),
    hE.comp ((hg.comp ComputableIn.fst).pair ComputableIn.snd), fun k ↦ hU (g k)⟩

/-- Unions over the members of a list of a c.e. open family are c.e. open, uniformly in the
list and in a parameter. -/
theorem IsCeOpenFamilyIn.biUnion_list {α κ : Type*} [Primcodable α] [Primcodable κ] [Inhabited κ]
    {U : α × κ → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsCeOpenFamilyIn P A fun aL : α × List κ ↦ ⋃ k ∈ aL.2, U (aL.1, k) := by
  obtain ⟨E, hE, hU⟩ := hU
  refine ⟨fun w ↦ ∃ m, m < w.1.2.length ∧ E ((w.1.1, w.1.2.getD m default), w.2), ?_, fun aL ↦ ?_⟩
  · have hlt : IsREIn A fun v : ((α × List κ) × (ℕ × ℚ)) × ℕ ↦ v.2 < v.1.1.2.length :=
      isREIn_of_computable_decide (Primrec.nat_lt.comp Primrec.snd
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))).decide.to_comp
    have hre : ComputableIn {charOracle A} fun v : ((α × List κ) × (ℕ × ℚ)) × ℕ ↦
        ((v.1.1.1, v.1.1.2.getD v.2 default), v.1.2) :=
      (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
        ((Primrec.list_getD default).to_comp.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd)).pair
        (Computable.snd.comp Computable.fst)).computableIn
    exact (hlt.and (hE.comp hre)).exists
  · ext y
    constructor
    · intro hy
      obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.mp hy
      obtain ⟨m, hm, hkm⟩ := List.mem_iff_getElem.mp hk
      rw [hU (aL.1, k)] at hyk
      obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hyk
      refine Set.mem_iUnion₂.mpr ⟨b, ⟨m, hm, ?_⟩, hyb⟩
      rw [List.getD_eq_getElem _ _ hm, hkm]
      exact hb
    · intro hy
      obtain ⟨b, ⟨m, hm, hb⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion₂.mpr ⟨aL.2.getD m default, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hm]
        exact List.getElem_mem hm
      · rw [hU]
        exact Set.mem_iUnion₂.mpr ⟨b, hb, hyb⟩

/-- An open set is the union of the basic balls it contains. -/
theorem isOpen_eq_biUnion_basicBall {U : Set X} (hU : IsOpen U) :
    U = ⋃ b ∈ {b : ℕ × ℚ | basicBall P b ⊆ U}, basicBall P b := by
  ext x
  constructor
  · intro hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense x (ε / 4) (by positivity)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    refine Set.mem_iUnion₂.mpr ⟨(k, q), ?_, Metric.mem_ball.mpr (hk.trans hq₁)⟩
    change basicBall P (k, q) ⊆ U
    intro z hz
    refine hεU (Metric.mem_ball.mpr ?_)
    have hz' : dist z (P.ι k) < q := hz
    have hk' : dist (P.ι k) x < ε / 4 := by
      rw [dist_comm]
      exact hk
    calc dist z x ≤ dist z (P.ι k) + dist (P.ι k) x := dist_triangle _ _ _
      _ < q + ε / 4 := add_lt_add hz' hk'
      _ < ε := by linarith
  · intro hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    exact hb hxb

/-- The union of a finite list of basic balls. Blueprint node `geo:effective-neighborhoods`. -/
def ballUnion (P : Presentation X) (L : List (ℕ × ℚ)) : Set X := ⋃ b ∈ L, basicBall P b

/-- The output neighborhoods are c.e. open uniformly in the output lists (finite unions of
basic balls with rational radii), which is what the section search of Chapter G needs.
Blueprint node `geo:effective-neighborhoods`. -/
theorem ballUnion_ceOpen : IsCeOpenFamilyIn P B fun L : List (ℕ × ℚ) ↦ ballUnion P L := by
  refine ⟨fun d ↦ d.2 ∈ d.1, ?_, fun _ ↦ rfl⟩
  have hdec : Computable fun d : List (ℕ × ℚ) × (ℕ × ℚ) ↦ decide (d.2 ∈ d.1) := by
    have h : Computable fun d : List (ℕ × ℚ) × (ℕ × ℚ) ↦
        decide (d.1.idxOf d.2 < d.1.length) :=
      (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.snd Primrec.fst)
        (Primrec.list_length.comp Primrec.fst))).to_comp
    refine h.of_eq fun d ↦ ?_
    simp only [List.idxOf_lt_length_iff]
  exact isREIn_of_computable_decide hdec

/-- The neighborhood of the transverse estimate can be replaced by a coded basic ball: there
are an ideal index `c` and a positive rational `rV` with `z ∈ basicBall P (c, rV) ⊆ V`. The
code `(c, rV)` is point-dependent localization data, independent of the durations.
Blueprint nodes `geo:flow-box-localization`, `geo:transverse-estimate`. -/
theorem exists_basicBall_code {z : X} {V : Set X} (hV : IsOpen V) (hz : z ∈ V) :
    ∃ (c : ℕ) (rV : ℚ), 0 < rV ∧ z ∈ basicBall P (c, rV) ∧ basicBall P (c, rV) ⊆ V := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV z hz
  obtain ⟨rV, hrV0, hrV⟩ := exists_rat_btwn (show (0 : ℝ) < r / 2 by positivity)
  obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp P.dense z rV hrV0
  refine ⟨c, rV, by exact_mod_cast hrV0, ?_, ?_⟩
  · change z ∈ Metric.ball (P.ι c) (rV : ℝ)
    exact Metric.mem_ball.mpr hc
  · intro y hy
    apply hball
    have hy' : dist y (P.ι c) < rV := Metric.mem_ball.mp hy
    rw [Metric.mem_ball]
    calc dist y z ≤ dist y (P.ι c) + dist (P.ι c) z := dist_triangle _ _ _
      _ < rV + rV := add_lt_add hy' (by rwa [dist_comm])
      _ < r := by linarith

end aux

section notions

variable (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)

/-- Finite intersections of c.e. open families are c.e. open, uniformly, above an oracle
computing the metric table: a ball tagged by the index is listed when rational distance
certificates place it inside a listed ball of each family. (The hypothesis `hP` cannot be
dropped: for a presentation whose metric table is not computable in `A`, the intersection of
two basic balls need not be an `A`-c.e. union of basic balls.) -/
theorem IsCeOpenFamilyIn.inter (hP : ComputablePresentationIn P A) {ι : Type*}
    [Primcodable ι] {U V : ι → Set X} (hU : IsCeOpenFamilyIn P A U)
    (hV : IsCeOpenFamilyIn P A V) : IsCeOpenFamilyIn P A fun i ↦ U i ∩ V i := by
  obtain ⟨E, hE, hU⟩ := hU
  obtain ⟨E', hE', hV⟩ := hV
  have hlt := birkhoff_computableIn_lt A _ hP
  -- a ball `d` tagged `i` is listed when it lies, with rational certificates, inside a listed
  -- ball of `U i` and a listed ball of `V i`
  let W : (ι × (ℕ × ℚ)) × ((ℕ × ℚ) × (ℕ × ℚ)) → Prop := fun w ↦
    (E (w.1.1, w.2.1) ∧ E' (w.1.1, w.2.2)) ∧ ((0 : ℚ) < w.1.2.2 ∧
      (dist (P.ι w.1.2.1) (P.ι w.2.1.1) < ((w.2.1.2 - w.1.2.2 : ℚ) : ℝ) ∧
        dist (P.ι w.1.2.1) (P.ι w.2.2.1) < ((w.2.2.2 - w.1.2.2 : ℚ) : ℝ)))
  have hW : IsREIn A W := by
    have h1 : IsREIn A fun w : (ι × (ℕ × ℚ)) × ((ℕ × ℚ) × (ℕ × ℚ)) ↦ E (w.1.1, w.2.1) :=
      hE.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)).computableIn
    have h2 : IsREIn A fun w : (ι × (ℕ × ℚ)) × ((ℕ × ℚ) × (ℕ × ℚ)) ↦ E' (w.1.1, w.2.2) :=
      hE'.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.comp Computable.snd)).computableIn
    have h3 : IsREIn A fun w : (ι × (ℕ × ℚ)) × ((ℕ × ℚ) × (ℕ × ℚ)) ↦ (0 : ℚ) < w.1.2.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
        (Computable.snd.comp (Computable.snd.comp Computable.fst)))
    have h4 : IsREIn A fun w : (ι × (ℕ × ℚ)) × ((ℕ × ℚ) × (ℕ × ℚ)) ↦
        dist (P.ι w.1.2.1) (P.ι w.2.1.1) < ((w.2.1.2 - w.1.2.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.fst.comp Computable.snd))).pair
        (computable₂_ratSub.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
    have h5 : IsREIn A fun w : (ι × (ℕ × ℚ)) × ((ℕ × ℚ) × (ℕ × ℚ)) ↦
        dist (P.ι w.1.2.1) (P.ι w.2.2.1) < ((w.2.2.2 - w.1.2.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd))).pair
        (computable₂_ratSub.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
    exact (h1.and h2).and (h3.and (h4.and h5))
  refine ⟨fun id ↦ ∃ bb', W (id, bb'), hW.exists, fun i ↦ ?_⟩
  ext y
  constructor
  · rintro ⟨hyU, hyV⟩
    rw [hU i] at hyU
    rw [hV i] at hyV
    obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hyU
    obtain ⟨b', hb', hyb'⟩ := Set.mem_iUnion₂.mp hyV
    have hyb₁ : dist y (P.ι b.1) < b.2 := hyb
    have hyb₂ : dist y (P.ι b'.1) < b'.2 := hyb'
    set r : ℝ := min ((b.2 : ℝ) - dist y (P.ι b.1)) ((b'.2 : ℝ) - dist y (P.ι b'.1)) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by linarith)
    have hr1 : r ≤ (b.2 : ℝ) - dist y (P.ι b.1) := min_le_left _ _
    have hr2 : r ≤ (b'.2 : ℝ) - dist y (P.ι b'.1) := min_le_right _ _
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp P.dense y (r / 4) (by positivity)
    obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
    have hky : dist (P.ι k) y < r / 4 := by rwa [dist_comm] at hk
    have htri₁ := dist_triangle (P.ι k) y (P.ι b.1)
    have htri₂ := dist_triangle (P.ι k) y (P.ι b'.1)
    refine Set.mem_iUnion₂.mpr ⟨(k, t), ⟨(b, b'), ⟨hb, hb'⟩, ?_, ?_, ?_⟩, ?_⟩
    · exact_mod_cast (show (0 : ℝ) < r / 4 by positivity).trans ht1
    · change dist (P.ι k) (P.ι b.1) < ((b.2 - t : ℚ) : ℝ)
      push_cast
      linarith
    · change dist (P.ι k) (P.ι b'.1) < ((b'.2 - t : ℚ) : ℝ)
      push_cast
      linarith
    · exact Metric.mem_ball.mpr (hk.trans ht1)
  · intro hy
    obtain ⟨⟨k, t⟩, ⟨⟨b, b'⟩, ⟨hb, hb'⟩, _, hkb, hkb'⟩, hyk⟩ := Set.mem_iUnion₂.mp hy
    have hyk' : dist y (P.ι k) < t := hyk
    have hkb₁ : dist (P.ι k) (P.ι b.1) < (b.2 : ℝ) - t := by
      have h : dist (P.ι k) (P.ι b.1) < ((b.2 - t : ℚ) : ℝ) := hkb
      push_cast at h
      exact h
    have hkb₂ : dist (P.ι k) (P.ι b'.1) < (b'.2 : ℝ) - t := by
      have h : dist (P.ι k) (P.ι b'.1) < ((b'.2 - t : ℚ) : ℝ) := hkb'
      push_cast at h
      exact h
    have htri₁ := dist_triangle y (P.ι k) (P.ι b.1)
    have htri₂ := dist_triangle y (P.ι k) (P.ι b'.1)
    constructor
    · rw [hU i]
      refine Set.mem_iUnion₂.mpr ⟨b, hb, ?_⟩
      change dist y (P.ι b.1) < b.2
      linarith
    · rw [hV i]
      refine Set.mem_iUnion₂.mpr ⟨b', hb', ?_⟩
      change dist y (P.ι b'.1) < b'.2
      linarith

/-- A ball about a computable point with a positive rational radius is c.e. open, uniformly in
the name and the radius. -/
theorem isCeOpenFamilyIn_ball (_hP : ComputablePresentationIn P A) :
    IsCeOpenFamilyIn P A fun d : ℕ × ℚ ↦ Metric.ball (P.ι d.1) (d.2 : ℝ) := by
  refine ⟨fun db ↦ db.2 = db.1,
    isREIn_of_computable_decide (Primrec.eq.comp Primrec.snd Primrec.fst).decide.to_comp,
    fun d ↦ ?_⟩
  ext y
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, exists_eq_left, basicBall]

/-- Monotonicity in the oracle. -/
theorem isCeOpenFamilyIn_mono {ι : Type*} [Primcodable ι] {B : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) {U : ι → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsCeOpenFamilyIn P B U := by
  obtain ⟨E, hE, hU⟩ := hU
  exact ⟨E, hE.mono_oracle hAB, hU⟩

end notions

end Kolmogorov.PointToSet
