/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.LocalEntropy
import KolmogorovMathlib.PointToSet.ComputableMetric.CeOpen
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface.OrbitExtension

/-!
# Bowen balls about ideal points are effectively open

Above an oracle `A` that computes the metric table of a presentation and represents the
dynamics `T`, the Bowen balls `B_n(x_i, T, q)` about ideal points with rational radii form a
c.e. open family, uniformly in `(n, i, q)`, and so do the complements of the closed Bowen balls
`B̄_n(x_i, T, q)`. This is consequence (M2) of §2.2 of E. Dinowitz, *Entropy of non-invariant
measures and orbit complexity of random points*.

The proof enumerates certificates: a chain of basic balls `c_0, …, c_{n-1}` with
`T (c_k) ⊆ c_{k+1}` witnessed by the representation of `T`, each `c_k` contained in the ball of
radius `q` about `T^k x_i` (respectively, the last one outside the closed ball) by a strict
inequality between computable reals. Every point of the Bowen ball lies in the first ball of
such a chain because all sufficiently small basic balls about a point are admissible at each
step.

* `bowenChainRep`, `exists_bowenChainRep`: a refined representation of `T` in which every
  sufficiently small basic ball about `x` is certified for each target ball containing `T x`.
* `isCeOpenFamilyIn_bowenChainSet`: for an enumerable step condition with this local property,
  the sets `bowenChainSet` of points whose iterates pass through allowed basic balls are c.e.
  open, uniformly (certificates are lists of basic balls, `IsREIn.list_forall_get`).
* `isCeOpenFamilyIn_bowenBall`: Bowen balls about ideal points are c.e. open, uniformly.
* `isCeOpenFamilyIn_compl_closedBowenBall`: so are the complements of closed Bowen balls.

Blueprint node `meas:bowen-ce-open`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X]

/-! ### Small basic balls and the refined representation -/

/-- Every point lies in basic balls of arbitrarily small positive rational radius. -/
theorem bowenChain_exists_small_ball (P : Presentation X) (z : X) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ × ℚ, 0 < b.2 ∧ (b.2 : ℝ) < δ ∧ z ∈ basicBall P b := by
  obtain ⟨t, ht0, htδ⟩ := exists_rat_btwn hδ
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp P.dense z t ht0
  exact ⟨(j, t), by exact_mod_cast ht0, htδ, hj⟩

/-- The refined representation of a map: the basic ball `b'` is certified, by a strict
inequality between an ideal distance and a rational, to lie inside a source ball `b` of the
representation `R` with target `c`. -/
def bowenChainRep (P : Presentation X) (R : (ℕ × ℚ) × (ℕ × ℚ) → Prop) :
    (ℕ × ℚ) × (ℕ × ℚ) → Prop := fun bc ↦
  ∃ b : ℕ × ℚ, R (b, bc.2) ∧ 0 < bc.1.2 ∧
    dist (P.ι bc.1.1) (P.ι b.1) < ((b.2 - bc.1.2 : ℚ) : ℝ)

/-- The refined representation is relatively enumerable above an oracle computing the metric
table. -/
theorem bowenChainRep_isREIn {P : Presentation X} {A : Set ℕ}
    {R : (ℕ × ℚ) × (ℕ × ℚ) → Prop} (hP : ComputablePresentationIn P A) (hR : IsREIn A R) :
    IsREIn A (bowenChainRep P R) := by
  have hlt := birkhoff_computableIn_lt A _ hP
  have h1 : IsREIn A fun w : ((ℕ × ℚ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦ R (w.2, w.1.2) :=
    hR.comp (Computable.snd.pair (Computable.snd.comp Computable.fst)).computableIn
  have h2 : IsREIn A fun w : ((ℕ × ℚ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦ (0 : ℚ) < w.1.1.2 :=
    isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp (Computable.fst.comp Computable.fst)))
  have h3 : IsREIn A fun w : ((ℕ × ℚ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
      dist (P.ι w.1.1.1) (P.ι w.2.1) < ((w.2.2 - w.1.1.2 : ℚ) : ℝ) :=
    hlt.comp (((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      (Computable.fst.comp Computable.snd)).pair
      (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
        (Computable.snd.comp (Computable.fst.comp Computable.fst)))).computableIn
  exact (h1.and (h2.and h3)).exists

/-- Soundness of the refined representation. -/
theorem bowenChainRep_sound {P : Presentation X} {T : X → X}
    {R : (ℕ × ℚ) × (ℕ × ℚ) → Prop}
    (hR : ∀ b c, R (b, c) → 0 < b.2 ∧ 0 < c.2 ∧ T '' basicBall P b ⊆ basicBall P c)
    {b' c : ℕ × ℚ} (h : bowenChainRep P R (b', c)) : T '' basicBall P b' ⊆ basicBall P c := by
  obtain ⟨b, hRb, _, hd⟩ := h
  rintro _ ⟨y, hy, rfl⟩
  apply (hR b c hRb).2.2
  refine ⟨y, ?_, rfl⟩
  have hy' : dist y (P.ι b'.1) < b'.2 := hy
  have hd' : dist (P.ι b'.1) (P.ι b.1) < (b.2 : ℝ) - b'.2 := by
    push_cast at hd
    exact hd
  change dist y (P.ι b.1) < b.2
  linarith [dist_triangle y (P.ι b'.1) (P.ι b.1)]

/-- Small-ball property of the refined representation: if `T x` lies in the target ball `c`,
every sufficiently small positive basic ball about `x` is certified for `c`. -/
theorem bowenChainRep_small {P : Presentation X} {T : X → X}
    {R : (ℕ × ℚ) × (ℕ × ℚ) → Prop}
    (hRc : ∀ x c, T x ∈ basicBall P c → ∃ b, R (b, c) ∧ x ∈ basicBall P b)
    {x : X} {c : ℕ × ℚ} (hx : T x ∈ basicBall P c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b' : ℕ × ℚ, 0 < b'.2 → (b'.2 : ℝ) < δ → x ∈ basicBall P b' →
      bowenChainRep P R (b', c) := by
  obtain ⟨b, hRb, hxb⟩ := hRc x c hx
  have hxb' : dist x (P.ι b.1) < b.2 := hxb
  refine ⟨(b.2 - dist x (P.ι b.1)) / 2, by linarith,
    fun b' hpos hsmall hxb'' ↦ ⟨b, hRb, hpos, ?_⟩⟩
  have h1 : dist x (P.ι b'.1) < b'.2 := hxb''
  push_cast
  linarith [dist_triangle (P.ι b'.1) x (P.ι b.1), dist_comm x (P.ι b'.1)]

/-- A represented map has a relatively enumerable, sound representation with the small-ball
property (the refined representation `bowenChainRep`). -/
theorem exists_bowenChainRep (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    ∃ R' : (ℕ × ℚ) × (ℕ × ℚ) → Prop, IsREIn A R' ∧
      (∀ b c, R' (b, c) → T '' basicBall P b ⊆ basicBall P c) ∧
      ∀ x c, T x ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ × ℚ, 0 < b.2 → (b.2 : ℝ) < δ →
        x ∈ basicBall P b → R' (b, c) := by
  obtain ⟨R, hRre, hRs, hRc⟩ := hTA
  exact ⟨bowenChainRep P R, bowenChainRep_isREIn hP hRre,
    fun _ _ h ↦ bowenChainRep_sound hRs h, fun _ _ hx ↦ bowenChainRep_small hRc hx⟩

/-! ### Chains of basic balls -/

/-- The set of points whose `k`-th iterate, for every `k < n`, lies in a basic ball allowed at
time `k` (for the parameter `a`) by the step condition `C`. -/
def bowenChainSet (P : Presentation X) (T : X → X) {κ : Type*}
    (C : (κ × ℕ) × (ℕ × ℚ) → Prop) (a : κ) (n : ℕ) : Set X :=
  {y | ∀ k < n, ∃ c, C ((a, k), c) ∧ T^[k] y ∈ basicBall P c}

/-- Soundness of chains: along a chain of basic balls linked by a sound relation, the iterates
of a point of the first ball stay in the successive balls. -/
theorem bowenChain_iterate_mem {P : Presentation X} {T : X → X}
    {R' : (ℕ × ℚ) × (ℕ × ℚ) → Prop}
    (hR'sound : ∀ b c, R' (b, c) → T '' basicBall P b ⊆ basicBall P c)
    {n : ℕ} {c : ℕ → ℕ × ℚ} (hc : ∀ k, k + 1 < n → R' (c k, c (k + 1)))
    {y : X} (hy : y ∈ basicBall P (c 0)) : ∀ k < n, T^[k] y ∈ basicBall P (c k) := by
  intro k
  induction k with
  | zero => intro _; exact hy
  | succ k ih =>
    intro hk
    rw [Function.iterate_succ_apply']
    exact hR'sound _ _ (hc k hk) ⟨_, ih (by omega), rfl⟩

/-- Completeness of chains: every point of `bowenChainSet` of positive order is the start of a
chain of positive basic balls, allowed at each time and linked by the relation `R'`. -/
theorem bowenChain_exists_chain {P : Presentation X} {T : X → X} {κ : Type*}
    {R' : (ℕ × ℚ) × (ℕ × ℚ) → Prop}
    (hR'small : ∀ x c, T x ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ × ℚ, 0 < b.2 →
      (b.2 : ℝ) < δ → x ∈ basicBall P b → R' (b, c))
    {C : (κ × ℕ) × (ℕ × ℚ) → Prop}
    (hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c'))
    {a : κ} {n : ℕ} {y : X} (hy : y ∈ bowenChainSet P T C a n) :
    ∃ c : ℕ → ℕ × ℚ, (∀ k < n, C ((a, k), c k) ∧ T^[k] y ∈ basicBall P (c k)) ∧
      ∀ k, k + 1 < n → R' (c k, c (k + 1)) := by
  -- an allowed small ball at time `j` below any prescribed radius
  have hsmall : ∀ j < n, ∀ δ : ℝ, 0 < δ → ∃ b : ℕ × ℚ, 0 < b.2 ∧ (b.2 : ℝ) < δ ∧
      C ((a, j), b) ∧ T^[j] y ∈ basicBall P b := by
    intro j hj δ hδ
    obtain ⟨c₀, hc₀, hyc₀⟩ := hy j hj
    obtain ⟨δ₂, hδ₂, hC₂⟩ := hCloc a j c₀ _ hc₀ hyc₀
    obtain ⟨b, hb0, hbδ, hyb⟩ :=
      bowenChain_exists_small_ball P (T^[j] y) (lt_min hδ hδ₂)
    exact ⟨b, hb0, hbδ.trans_le (min_le_left _ _), hC₂ b hb0 (hbδ.trans_le (min_le_right _ _))
      hyb, hyb⟩
  have key : ∀ m j, j + m + 1 = n → ∃ c : ℕ → ℕ × ℚ,
      (∀ k, j ≤ k → k < n → C ((a, k), c k) ∧ T^[k] y ∈ basicBall P (c k)) ∧
      ∀ k, j ≤ k → k + 1 < n → R' (c k, c (k + 1)) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      obtain ⟨b, _, _, hCb, hyb⟩ := hsmall j (by omega) 1 one_pos
      refine ⟨fun _ ↦ b, fun k hjk hkn ↦ ?_, fun k hjk hkn ↦ by omega⟩
      obtain rfl : k = j := by omega
      exact ⟨hCb, hyb⟩
    | succ m ih =>
      intro j hj
      obtain ⟨c, hc, hcR⟩ := ih (j + 1) (by omega)
      have hmem := (hc (j + 1) le_rfl (by omega)).2
      rw [Function.iterate_succ_apply'] at hmem
      obtain ⟨δ₁, hδ₁, hR₁⟩ := hR'small _ _ hmem
      obtain ⟨b, hb0, hbδ, hCb, hyb⟩ := hsmall j (by omega) δ₁ hδ₁
      refine ⟨fun k ↦ if k = j then b else c k, fun k hjk hkn ↦ ?_, fun k hjk hkn ↦ ?_⟩
      · by_cases hkj : k = j
        · simp only [hkj, ↓reduceIte]
          exact ⟨hCb, hyb⟩
        · simp only [hkj, ↓reduceIte]
          exact hc k (by omega) hkn
      · have hk1 : k + 1 ≠ j := by omega
        by_cases hkj : k = j
        · subst hkj
          simp only [hk1, ↓reduceIte]
          exact hR₁ b hb0 hbδ hyb
        · simp only [hkj, hk1, ↓reduceIte]
          exact hcR k (by omega) hkn
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨fun _ ↦ (0, 0), fun k hk ↦ by omega, fun k hk ↦ by omega⟩
  · obtain ⟨c, hc, hcR⟩ := key (n - 1) 0 (by omega)
    exact ⟨c, fun k hk ↦ hc k (Nat.zero_le k) hk, fun k hk ↦ hcR k (Nat.zero_le k) hk⟩

/-- Chains of basic balls give c.e. open families: for a relatively enumerable, sound relation
`R'` with the small-ball property and a relatively enumerable step condition `C` with the local
property, the sets `bowenChainSet P T C a n` are c.e. open uniformly in `(a, n)`. -/
theorem isCeOpenFamilyIn_bowenChainSet {κ : Type*} [Primcodable κ] (P : Presentation X)
    (T : X → X) (A : Set ℕ) {R' : (ℕ × ℚ) × (ℕ × ℚ) → Prop} (hR're : IsREIn A R')
    (hR'sound : ∀ b c, R' (b, c) → T '' basicBall P b ⊆ basicBall P c)
    (hR'small : ∀ x c, T x ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ × ℚ, 0 < b.2 →
      (b.2 : ℝ) < δ → x ∈ basicBall P b → R' (b, c))
    {C : (κ × ℕ) × (ℕ × ℚ) → Prop} (hCre : IsREIn A C)
    (hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c')) :
    IsCeOpenFamilyIn P A fun an : κ × ℕ ↦ bowenChainSet P T C an.1 an.2 := by
  let d0 : ℕ × ℚ := (0, 0)
  -- the certificate: a list of basic balls of length `n` starting with `b`
  let G : ((κ × ℕ) × (ℕ × ℚ)) × List (ℕ × ℚ) → Prop := fun v ↦
    (v.2.length = v.1.1.2 ∧ (v.1.1.2 = 0 ∨ v.2.getD 0 d0 = v.1.2)) ∧
      ((∀ k (h : k < v.2.length), C ((v.1.1.1, k), v.2.get ⟨k, h⟩)) ∧
        ∀ k (h : k < v.2.length),
          v.2.length ≤ k + 1 ∨ R' (v.2.get ⟨k, h⟩, v.2.getD (k + 1) d0))
  have hG : IsREIn A G := by
    have e1 : IsREIn A fun v : ((κ × ℕ) × (ℕ × ℚ)) × List (ℕ × ℚ) ↦
        v.2.length = v.1.1.2 :=
      isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).decide.to_comp
    have e2 : IsREIn A fun v : ((κ × ℕ) × (ℕ × ℚ)) × List (ℕ × ℚ) ↦ v.1.1.2 = 0 :=
      isREIn_of_computable_decide (Primrec.eq.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 0)).decide.to_comp
    have e3 : IsREIn A fun v : ((κ × ℕ) × (ℕ × ℚ)) × List (ℕ × ℚ) ↦
        v.2.getD 0 d0 = v.1.2 :=
      isREIn_of_computable_decide (Primrec.eq.comp
        ((Primrec.list_getD d0).comp Primrec.snd (Primrec.const 0))
        (Primrec.snd.comp Primrec.fst)).decide.to_comp
    have hF2 : IsREIn A fun x : κ × ℕ × (ℕ × ℚ) ↦ C ((x.1, x.2.1), x.2.2) :=
      hCre.comp ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
        (Computable.snd.comp Computable.snd)).computableIn
    have e4 : IsREIn A fun v : ((κ × ℕ) × (ℕ × ℚ)) × List (ℕ × ℚ) ↦
        ∀ k (h : k < v.2.length), C ((v.1.1.1, k), v.2.get ⟨k, h⟩) :=
      hF2.list_forall_get.comp
        ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
          Computable.snd).computableIn
    have hF3 : IsREIn A fun x : List (ℕ × ℚ) × ℕ × (ℕ × ℚ) ↦
        x.1.length ≤ x.2.1 + 1 ∨ R' (x.2.2, x.1.getD (x.2.1 + 1) d0) := by
      have f1 : IsREIn A fun x : List (ℕ × ℚ) × ℕ × (ℕ × ℚ) ↦ x.1.length ≤ x.2.1 + 1 :=
        isREIn_of_computable_decide (Primrec.nat_le.comp
          (Primrec.list_length.comp Primrec.fst)
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.const 1))).decide.to_comp
      have f2 : IsREIn A fun x : List (ℕ × ℚ) × ℕ × (ℕ × ℚ) ↦
          R' (x.2.2, x.1.getD (x.2.1 + 1) d0) :=
        hR're.comp ((Computable.snd.comp Computable.snd).pair
          ((Primrec.list_getD d0).comp Primrec.fst
            (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
              (Primrec.const 1))).to_comp).computableIn
      exact f1.or f2
    have e5 : IsREIn A fun v : ((κ × ℕ) × (ℕ × ℚ)) × List (ℕ × ℚ) ↦
        ∀ k (h : k < v.2.length),
          v.2.length ≤ k + 1 ∨ R' (v.2.get ⟨k, h⟩, v.2.getD (k + 1) d0) :=
      hF3.list_forall_get.comp (Computable.snd.pair Computable.snd).computableIn
    exact (e1.and (e2.or e3)).and (e4.and e5)
  refine ⟨fun w ↦ ∃ L, G (w, L), hG.exists, fun an ↦ ?_⟩
  obtain ⟨a, n⟩ := an
  ext y
  constructor
  · intro hy
    rcases Nat.eq_zero_or_pos n with hn | hn
    · obtain ⟨b, _, _, hyb⟩ := bowenChain_exists_small_ball P y one_pos
      refine Set.mem_iUnion₂.mpr ⟨b, ⟨[], ⟨hn.symm, Or.inl hn⟩, fun k h ↦ ?_, fun k h ↦ ?_⟩, hyb⟩
      · exact (Nat.not_lt_zero k h).elim
      · exact (Nat.not_lt_zero k h).elim
    · obtain ⟨c, hc, hcR⟩ := bowenChain_exists_chain hR'small hCloc hy
      let L : List (ℕ × ℚ) := (List.range n).map c
      have hlen : L.length = n := by simp [L]
      have hget : ∀ k (h : k < L.length), L.get ⟨k, h⟩ = c k := by
        intro k h
        simp [L]
      have hgetD : ∀ k, k < n → L.getD k d0 = c k := by
        intro k hk
        rw [List.getD_eq_getElem _ _ (hlen ▸ hk)]
        simp [L]
      refine Set.mem_iUnion₂.mpr ⟨c 0, ⟨L, ⟨hlen, Or.inr (hgetD 0 hn)⟩, fun k h ↦ ?_,
        fun k h ↦ ?_⟩, (hc 0 hn).2⟩
      · rw [hget]
        exact (hc k (hlen ▸ h)).1
      · have hk' : k < n := hlen ▸ h
        by_cases hk : n ≤ k + 1
        · left
          change L.length ≤ k + 1
          rw [hlen]
          exact hk
        · right
          change R' (L.get ⟨k, h⟩, L.getD (k + 1) d0)
          rw [hget, hgetD (k + 1) (by omega)]
          exact hcR k (by omega)
  · intro hy
    obtain ⟨b, ⟨L, ⟨hlen, hb0⟩, hC, hR⟩, hyb⟩ := Set.mem_iUnion₂.mp hy
    dsimp only at hlen hb0 hC hR
    intro k hk
    have hb : L.getD 0 d0 = b := hb0.resolve_left (by omega)
    have hget : ∀ k (h : k < L.length), L.get ⟨k, h⟩ = L.getD k d0 := by
      intro k h
      rw [List.getD_eq_getElem _ _ h, List.get_eq_getElem]
    have hchain : ∀ j, j + 1 < n → R' (L.getD j d0, L.getD (j + 1) d0) := by
      intro j hj
      have h := (hR j (by omega)).resolve_left (by omega)
      rwa [hget] at h
    have hmem := bowenChain_iterate_mem hR'sound hchain (hb ▸ hyb) k hk
    refine ⟨L.getD k d0, ?_, hmem⟩
    have h := hC k (by omega)
    rwa [hget] at h

/-! ### The two step conditions -/

/-- A basic ball certified inside the ball of radius `q` about `x` keeps its points inside
that ball. -/
theorem bowenStep_dist_lt {P : Presentation X} {x z : X} {q : ℚ} {c : ℕ × ℚ}
    (hc : dist x (P.ι c.1) < ((q - c.2 : ℚ) : ℝ)) (hz : z ∈ basicBall P c) :
    dist x z < q := by
  have hz' : dist z (P.ι c.1) < c.2 := hz
  push_cast at hc
  linarith [dist_triangle x (P.ι c.1) z, dist_comm z (P.ι c.1)]

/-- Every sufficiently small basic ball about a point of the ball of radius `q` about `x` is
certified inside that ball. -/
theorem bowenStep_small_lt {P : Presentation X} {x z : X} {q : ℚ} (h : dist x z < q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℕ × ℚ, (c.2 : ℝ) < δ → z ∈ basicBall P c →
      dist x (P.ι c.1) < ((q - c.2 : ℚ) : ℝ) := by
  refine ⟨(q - dist x z) / 2, by linarith, fun c hc hz ↦ ?_⟩
  have hz' : dist z (P.ι c.1) < c.2 := hz
  push_cast
  linarith [dist_triangle x z (P.ι c.1)]

/-- A basic ball certified outside the closed ball of radius `q` about `x` keeps its points
outside that closed ball. -/
theorem bowenStep_lt_dist {P : Presentation X} {x z : X} {q : ℚ} {c : ℕ × ℚ}
    (hc : ((q + c.2 : ℚ) : ℝ) < dist x (P.ι c.1)) (hz : z ∈ basicBall P c) :
    (q : ℝ) < dist x z := by
  have hz' : dist z (P.ι c.1) < c.2 := hz
  push_cast at hc
  linarith [dist_triangle x z (P.ι c.1)]

/-- Every sufficiently small basic ball about a point outside the closed ball of radius `q`
about `x` is certified outside that closed ball. -/
theorem bowenStep_small_gt {P : Presentation X} {x z : X} {q : ℚ} (h : (q : ℝ) < dist x z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℕ × ℚ, (c.2 : ℝ) < δ → z ∈ basicBall P c →
      ((q + c.2 : ℚ) : ℝ) < dist x (P.ι c.1) := by
  refine ⟨(dist x z - q) / 2, by linarith, fun c hc hz ↦ ?_⟩
  have hz' : dist z (P.ι c.1) < c.2 := hz
  push_cast
  linarith [dist_triangle x (P.ι c.1) z, dist_comm z (P.ι c.1)]

/-- (M2), open half: the Bowen balls about ideal points with rational radii are c.e. open
relative to an oracle computing the metric table and representing the dynamics, uniformly in
the order, the centre and the radius. Blueprint node `meas:bowen-ce-open`. -/
theorem isCeOpenFamilyIn_bowenBall (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    IsCeOpenFamilyIn P A fun d : ℕ × ℕ × ℚ ↦ bowenBall T d.1 (P.ι d.2.1) (d.2.2 : ℝ) := by
  have hlt := birkhoff_computableIn_lt A _
    (isComputableRealFamilyIn_dist_iterate_ideal P T A hP hTA)
  obtain ⟨R', hR're, hR's, hR'small⟩ := exists_bowenChainRep P T A hP hTA
  -- step condition for the parameter `(i, q)` at time `k`
  let C : ((ℕ × ℚ) × ℕ) × (ℕ × ℚ) → Prop := fun w ↦
    0 < w.2.2 ∧ dist (T^[w.1.2] (P.ι w.1.1.1)) (P.ι w.2.1) < ((w.1.1.2 - w.2.2 : ℚ) : ℝ)
  have hCre : IsREIn A C :=
    (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp Computable.snd))).and
      (hlt.comp (((Computable.snd.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
          (Computable.fst.comp Computable.snd))).pair
        (computable₂_ratSub.comp (Computable.snd.comp (Computable.fst.comp Computable.fst))
          (Computable.snd.comp Computable.snd))).computableIn)
  have hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c') := by
    rintro a k c z ⟨_, hc⟩ hz
    obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_lt (P := P) (bowenStep_dist_lt hc hz)
    exact ⟨δ, hδ, fun c' hc'0 hc'δ hzc' ↦ ⟨hc'0, hsmall c' hc'δ hzc'⟩⟩
  have H := isCeOpenFamilyIn_bowenChainSet P T A hR're hR's hR'small hCre hCloc
  have heq : ∀ (i : ℕ) (q : ℚ) (n : ℕ),
      bowenChainSet P T C (i, q) n = bowenBall T n (P.ι i) (q : ℝ) := by
    intro i q n
    ext y
    rw [mem_bowenBall_iff]
    constructor
    · rintro hy k hk
      obtain ⟨c, ⟨_, hc⟩, hyc⟩ := hy k hk
      exact bowenStep_dist_lt hc hyc
    · intro hy k hk
      obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_lt (P := P) (hy k hk)
      obtain ⟨c, hc0, hcδ, hyc⟩ := bowenChain_exists_small_ball P (T^[k] y) hδ
      exact ⟨c, ⟨hc0, hsmall c hcδ hyc⟩, hyc⟩
  have hg : Computable fun d : ℕ × ℕ × ℚ ↦ ((d.2.1, d.2.2), d.1) :=
    ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd)).pair
      Computable.fst
  have h := H.comp hg
  have hfun : (fun d : ℕ × ℕ × ℚ ↦ bowenBall T d.1 (P.ι d.2.1) (d.2.2 : ℝ)) =
      fun d ↦ bowenChainSet P T C ((d.2.1, d.2.2), d.1).1 ((d.2.1, d.2.2), d.1).2 :=
    funext fun d ↦ (heq d.2.1 d.2.2 d.1).symm
  rw [hfun]
  exact h

/-- (M2), closed half: the complements of the closed Bowen balls about ideal points with
rational radii are c.e. open, uniformly in the order, the centre and the radius.
Blueprint node `meas:bowen-ce-open`. -/
theorem isCeOpenFamilyIn_compl_closedBowenBall (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    IsCeOpenFamilyIn P A fun d : ℕ × ℕ × ℚ ↦
      (closedBowenBall T d.1 (P.ι d.2.1) (d.2.2 : ℝ))ᶜ := by
  have hgt := birkhoff_computableIn_gt A _
    (isComputableRealFamilyIn_dist_iterate_ideal P T A hP hTA)
  obtain ⟨R', hR're, hR's, hR'small⟩ := exists_bowenChainRep P T A hP hTA
  -- step condition for the parameter `((i, q), k₀)` at time `k`: no constraint before `k₀`,
  -- outside the closed ball of radius `q` about `T^[k₀] (P.ι i)` from time `k₀` on
  let C : (((ℕ × ℚ) × ℕ) × ℕ) × (ℕ × ℚ) → Prop := fun w ↦
    0 < w.2.2 ∧ (w.1.2 < w.1.1.2 ∨
      ((w.1.1.1.2 + w.2.2 : ℚ) : ℝ) < dist (T^[w.1.1.2] (P.ι w.1.1.1.1)) (P.ι w.2.1))
  have hCre : IsREIn A C :=
    (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp Computable.snd))).and
      ((isREIn_of_computable_decide (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).decide.to_comp).or
      (hgt.comp (((Computable.snd.comp (Computable.fst.comp Computable.fst)).pair
        ((Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))).pair
          (Computable.fst.comp Computable.snd))).pair
        (computable₂_ratAdd.comp
          (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
          (Computable.snd.comp Computable.snd))).computableIn))
  have hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c') := by
    rintro a k c z ⟨_, hc | hc⟩ hz
    · exact ⟨1, one_pos, fun c' hc'0 _ _ ↦ ⟨hc'0, Or.inl hc⟩⟩
    · obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_gt (P := P) (bowenStep_lt_dist hc hz)
      exact ⟨δ, hδ, fun c' hc'0 hc'δ hzc' ↦ ⟨hc'0, Or.inr (hsmall c' hc'δ hzc')⟩⟩
  have H := isCeOpenFamilyIn_bowenChainSet P T A hR're hR's hR'small hCre hCloc
  have heq : ∀ (i : ℕ) (q : ℚ) (k₀ : ℕ), bowenChainSet P T C ((i, q), k₀) (k₀ + 1) =
      {y | (q : ℝ) < dist (T^[k₀] (P.ι i)) (T^[k₀] y)} := by
    intro i q k₀
    ext y
    constructor
    · intro hy
      obtain ⟨c, ⟨_, hc⟩, hyc⟩ := hy k₀ (Nat.lt_succ_self k₀)
      exact bowenStep_lt_dist (hc.resolve_left (lt_irrefl k₀)) hyc
    · intro hy k hk
      rcases Nat.lt_or_ge k k₀ with hkk | hkk
      · obtain ⟨c, hc0, _, hyc⟩ := bowenChain_exists_small_ball P (T^[k] y) one_pos
        exact ⟨c, ⟨hc0, Or.inl hkk⟩, hyc⟩
      · obtain rfl : k = k₀ := by omega
        obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_gt (P := P) hy
        obtain ⟨c, hc0, hcδ, hyc⟩ := bowenChain_exists_small_ball P (T^[k] y) hδ
        exact ⟨c, ⟨hc0, Or.inr (hsmall c hcδ hyc)⟩, hyc⟩
  have hg : Computable fun w : (ℕ × ℕ × ℚ) × ℕ ↦ (((w.1.2.1, w.1.2.2), w.2), w.2 + 1) :=
    ((((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (Computable.snd.comp (Computable.snd.comp Computable.fst))).pair Computable.snd).pair
      (Primrec.succ.comp Primrec.snd).to_comp)
  have hp : Computable fun w : (ℕ × ℕ × ℚ) × ℕ ↦ decide (w.2 < w.1.1) :=
    (Primrec.nat_lt.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).decide.to_comp
  have h := ((H.comp hg).ite (p := fun w : (ℕ × ℕ × ℚ) × ℕ ↦ w.2 < w.1.1) hp).iUnion
  have hfun : (fun d : ℕ × ℕ × ℚ ↦ (closedBowenBall T d.1 (P.ι d.2.1) (d.2.2 : ℝ))ᶜ) =
      fun d ↦ ⋃ k₀ : ℕ, if k₀ < d.1 then
        bowenChainSet P T C ((d.2.1, d.2.2), k₀) (k₀ + 1) else ∅ := by
    funext d
    ext y
    rw [Set.mem_compl_iff, mem_closedBowenBall_iff, Set.mem_iUnion]
    constructor
    · intro hy
      push Not at hy
      obtain ⟨k, hk, hlt⟩ := hy
      refine ⟨k, ?_⟩
      simp only [hk, ↓reduceIte, heq]
      exact hlt
    · rintro ⟨k, hk⟩ hall
      by_cases hkn : k < d.1
      · simp only [hkn, ↓reduceIte, heq] at hk
        exact absurd (hall k hkn) (not_le.mpr hk)
      · simp only [hkn, ↓reduceIte] at hk
        exact hk.elim
  rw [hfun]
  exact h

end Kolmogorov.PointToSet
