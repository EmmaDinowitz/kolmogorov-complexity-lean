/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.CeOpen

/-!
# Effective compactness

A compact set is relatively computably compact when its containment in a finite union of
coded basic balls is semidecidable (`IsComputablyCompactIn`); a family indexed by a primcodable
type is computably compact uniformly in the index (`IsComputablyCompactFamilyIn`). The one
consequence used by every effective search is that containment of a computably compact set in
a member of a c.e. open family is semidecidable, uniformly in both indices
(`IsComputablyCompactFamilyIn.subset_ceOpen_isREIn`): enumerate the balls of the open set in
stages and ask the compactness certificate about each finite stage.
Blueprint node `eff:compact`.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A compact set is relatively computably compact when containment in a finite union of
basic balls is semidecidable. Blueprint node `geo:effective-data` (item 4). -/
def IsComputablyCompactIn (P : Presentation X) (A : Set ℕ) (K : Set X) : Prop :=
  IsCompact K ∧ IsREIn A fun L : List (ℕ × ℚ) ↦ K ⊆ ⋃ b ∈ L, basicBall P b

/-- A family of compact sets indexed by a primcodable type, computably compact uniformly in
the index. Blueprint node `geo:effective-data` (item 4). -/
def IsComputablyCompactFamilyIn {ι : Type*} [Primcodable ι] (P : Presentation X) (A : Set ℕ)
    (K : ι → Set X) : Prop :=
  (∀ i, IsCompact (K i)) ∧
    IsREIn A fun d : ι × List (ℕ × ℚ) ↦ K d.1 ⊆ ⋃ b ∈ d.2, basicBall P b

section aux

variable {P : Presentation X} {Q : Presentation Y} {A B : Set ℕ}

/-- Reindexing a computably compact family along a computable map. -/
theorem IsComputablyCompactFamilyIn.comp {ι κ : Type*} [Primcodable ι] [Primcodable κ]
    {K : ι → Set X} (hK : IsComputablyCompactFamilyIn P A K) {g : κ → ι} (hg : Computable g) :
    IsComputablyCompactFamilyIn P A fun k ↦ K (g k) :=
  ⟨fun k ↦ hK.1 (g k), hK.2.comp ((hg.comp Computable.fst).pair Computable.snd).computableIn⟩

/-- Containment of the members of a computably compact family in the members of a c.e. open
family is semidecidable, uniformly in both indices. -/
theorem IsComputablyCompactFamilyIn.subset_ceOpen_isREIn {κ ι : Type*} [Primcodable κ]
    [Primcodable ι] {K : κ → Set X} (hK : IsComputablyCompactFamilyIn P A K) {U : ι → Set X}
    (hU : IsCeOpenFamilyIn P A U) : IsREIn A fun d : κ × ι ↦ K d.1 ⊆ U d.2 := by
  obtain ⟨hKc, hKre⟩ := hK
  obtain ⟨E, hE, hU⟩ := hU
  obtain ⟨e, he, henum⟩ := (relative_enumeration A E).mp hE
  -- the balls enumerated for the index `i` within the first `t` stages, as a list
  let step : ι × List (ℕ × ℚ) × Option (ι × (ℕ × ℚ)) → List (ℕ × ℚ) := fun w ↦
    Option.casesOn (motive := fun _ ↦ List (ℕ × ℚ)) w.2.2 w.2.1 fun v ↦
      if Encodable.encode v.1 = Encodable.encode w.1 then v.2 :: w.2.1 else w.2.1
  have hstep : Computable step := by
    refine Computable.option_casesOn (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd) (Primrec.to_comp ?_)
    exact Primrec.ite
      (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.encode.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  let L : ι × ℕ → List (ℕ × ℚ) := fun it ↦
    @Nat.rec (fun _ ↦ List (ℕ × ℚ)) [] (fun s ih ↦ step (it.1, ih, e s)) it.2
  have hL : ComputableIn {charOracle A} L := by
    refine ComputableIn.nat_rec (f := fun it : ι × ℕ ↦ it.2) (g := fun _ ↦ ([] : List (ℕ × ℚ)))
      (h := fun it sih ↦ step (it.1, sih.2, e sih.1)) ComputableIn.snd (ComputableIn.const [])
      (ComputableIn₂.mk ?_)
    exact hstep.computableIn.comp ((ComputableIn.fst.comp ComputableIn.fst).pair
      ((ComputableIn.snd.comp ComputableIn.snd).pair
        (he.comp (ComputableIn.fst.comp ComputableIn.snd))))
  have hmem : ∀ (i : ι) (t : ℕ) (b : ℕ × ℚ), b ∈ L (i, t) ↔ ∃ s < t, e s = some (i, b) := by
    intro i t b
    induction t with
    | zero => simp [L]
    | succ t ih =>
      have hstep_eq : L (i, t + 1) = step (i, L (i, t), e t) := rfl
      rw [hstep_eq]
      cases het : e t with
      | none =>
        change b ∈ L (i, t) ↔ _
        rw [ih]
        constructor
        · rintro ⟨s, hs, hes⟩
          exact ⟨s, by omega, hes⟩
        · rintro ⟨s, hs, hes⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
          · exact ⟨s, hs, hes⟩
          · rw [het] at hes
            exact absurd hes (by simp)
      | some v =>
        change b ∈ (if Encodable.encode v.1 = Encodable.encode i then v.2 :: L (i, t) else L (i, t))
          ↔ _
        split_ifs with hv
        · have hv' : v.1 = i := Encodable.encode_injective hv
          rw [List.mem_cons, ih]
          constructor
          · rintro (rfl | ⟨s, hs, hes⟩)
            · exact ⟨t, Nat.lt_succ_self t, by rw [het, ← hv']⟩
            · exact ⟨s, by omega, hes⟩
          · rintro ⟨s, hs, hes⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
            · exact Or.inr ⟨s, hs, hes⟩
            · rw [het] at hes
              exact Or.inl (by rw [Option.some_injective _ hes])
        · rw [ih]
          constructor
          · rintro ⟨s, hs, hes⟩
            exact ⟨s, by omega, hes⟩
          · rintro ⟨s, hs, hes⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
            · exact ⟨s, hs, hes⟩
            · rw [het] at hes
              have hv2 : v = (i, b) := Option.some_injective _ hes
              exact (hv (by rw [hv2])).elim
  have hmono : ∀ i t t' b, t ≤ t' → b ∈ L (i, t) → b ∈ L (i, t') := by
    intro i t t' b htt hb
    obtain ⟨s, hs, hes⟩ := (hmem i t b).mp hb
    exact (hmem i t' b).mpr ⟨s, by omega, hes⟩
  have hiff : ∀ k i, K k ⊆ U i ↔ ∃ t, K k ⊆ ⋃ b ∈ L (i, t), basicBall P b := by
    intro k i
    constructor
    · intro hKU
      have hcov : K k ⊆ ⋃ b ∈ {b | E (i, b)}, basicBall P b := by
        rw [← hU i]
        exact hKU
      obtain ⟨F, hFE, hFfin, hKF⟩ :=
        (hKc k).elim_finite_subcover_image (fun b _ ↦ Metric.isOpen_ball) hcov
      have hstage : ∀ S : Finset (ℕ × ℚ), (∀ b ∈ S, E (i, b)) →
          ∃ t, ∀ b ∈ S, b ∈ L (i, t) := by
        intro S
        refine Finset.induction_on S ?_ ?_
        · exact fun _ ↦ ⟨0, fun b hb ↦ by simp at hb⟩
        · intro b S _ ih h
          obtain ⟨t, ht⟩ := ih fun b' hb' ↦ h b' (Finset.mem_insert_of_mem hb')
          obtain ⟨s, hs⟩ := (henum (i, b)).mp (h b (Finset.mem_insert_self b S))
          refine ⟨max t (s + 1), fun b' hb' ↦ ?_⟩
          rcases Finset.mem_insert.mp hb' with rfl | hb'
          · exact (hmem i _ b').mpr ⟨s, by omega, hs⟩
          · exact hmono i t _ b' (le_max_left _ _) (ht b' hb')
      obtain ⟨t, ht⟩ := hstage hFfin.toFinset fun b hb ↦ hFE (hFfin.mem_toFinset.mp hb)
      refine ⟨t, hKF.trans (Set.iUnion₂_subset fun b hb ↦ ?_)⟩
      exact Set.subset_iUnion₂ (s := fun b _ ↦ basicBall P b) b
        (ht b (hFfin.mem_toFinset.mpr hb))
    · rintro ⟨t, ht⟩
      refine ht.trans (Set.iUnion₂_subset fun b hb ↦ ?_)
      obtain ⟨s, _, hes⟩ := (hmem i t b).mp hb
      have hEb : E (i, b) := (henum (i, b)).mpr ⟨s, hes⟩
      rw [hU i]
      exact Set.subset_iUnion₂ (s := fun b _ ↦ basicBall P b) b hEb
  have heq : (fun d : κ × ι ↦ K d.1 ⊆ U d.2) =
      fun d ↦ ∃ t, K d.1 ⊆ ⋃ b ∈ L (d.2, t), basicBall P b :=
    funext fun d ↦ propext (hiff d.1 d.2)
  rw [heq]
  exact (hKre.comp ((ComputableIn.fst.comp ComputableIn.fst).pair
    (hL.comp ((ComputableIn.snd.comp ComputableIn.fst).pair ComputableIn.snd)))).exists

end aux

section notions

variable (P : Presentation X) (Q : Presentation Y) (A : Set ℕ)

/-- Containment of a computably compact set in a c.e. open set is semidecidable, uniformly in
the c.e. presentation: this is the search step of `geo:localization`.
Blueprint node `geo:effective-data` (item 4). -/
theorem IsComputablyCompactIn.subset_ceOpen_isREIn {K : Set X} (hK : IsComputablyCompactIn P A K)
    {ι : Type*} [Primcodable ι] {U : ι → Set X} (hU : IsCeOpenFamilyIn P A U) :
    IsREIn A fun i : ι ↦ K ⊆ U i := by
  have hK' : IsComputablyCompactFamilyIn P A fun _ : Unit ↦ K :=
    ⟨fun _ ↦ hK.1, hK.2.comp ComputableIn.snd⟩
  exact (hK'.subset_ceOpen_isREIn hU).comp ((Computable.const ()).pair Computable.id).computableIn

/-- Monotonicity in the oracle. -/
theorem isComputablyCompactFamilyIn_mono {ι : Type*} [Primcodable ι] {B : Set ℕ}
    (hAB : charOracle A ≤ᵀ charOracle B) {K : ι → Set X}
    (hK : IsComputablyCompactFamilyIn P A K) : IsComputablyCompactFamilyIn P B K :=
  ⟨hK.1, hK.2.mono_oracle hAB⟩

end notions

end Kolmogorov.PointToSet
