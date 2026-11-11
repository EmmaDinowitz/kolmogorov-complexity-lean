/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.Basic
import KolmogorovMathlib.Oracle.Universal.Enumeration

/-!
# Relatively computable choice along an enumeration

A relatively enumerable relation `G ⊆ α × β` admits a dovetailed search: the program that runs
an enumeration of `G` and returns the second component of the first pair listed with the
requested first component is partial recursive in the oracle, halts exactly on the indices that
have a witness, and returns a witness (`IsREIn.exists_partrecIn_choice`). When every index has a
witness the search is total and relatively computable (`IsREIn.exists_computableIn_choice`).
Every decoder of the effective localization arguments is an instance of this search applied to
a certificate predicate. Blueprint node `eff:search`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

variable {A : Set ℕ}

/-- Relative enumerability admits partial relatively computable choice: a dovetailed search
along an enumeration halts on an index exactly when it has a witness, and returns one. -/
theorem IsREIn.exists_partrecIn_choice {α β : Type*} [Primcodable α] [Primcodable β]
    {G : α × β → Prop} (hG : IsREIn A G) :
    ∃ g : α →. β, PartrecIn {charOracle A} g ∧ (∀ a, (g a).Dom ↔ ∃ b, G (a, b)) ∧
      ∀ a b, b ∈ g a → G (a, b) := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration A G).mp hG
  let test : α → ℕ → Option β := fun a t ↦
    (e t).bind fun w ↦ if Encodable.encode w.1 = Encodable.encode a then some w.2 else none
  have htest : ComputableIn₂ {charOracle A} test := by
    have hpost : Computable fun p : α × Option (α × β) ↦
        p.2.bind fun w ↦
          if Encodable.encode w.1 = Encodable.encode p.1 then some w.2 else none := by
      refine Computable.option_bind Computable.snd ?_
      have hc : Primrec fun pw : (α × Option (α × β)) × (α × β) ↦
          if Encodable.encode pw.2.1 = Encodable.encode pw.1.1 then some pw.2.2 else none :=
        Primrec.ite
          (Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
            (Primrec.encode.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
      exact hc.to_comp
    exact ComputableIn₂.mk
      (hpost.computableIn.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd)))
  have hsound : ∀ a b t, b ∈ test a t → G (a, b) := by
    intro a b t ht
    cases het : e t with
    | none => simp [test, het] at ht
    | some w =>
      simp only [test, het, Option.bind_some] at ht
      split_ifs at ht with hw
      · have hw1 : w.1 = a := Encodable.encode_injective hw
        have hw2 : b = w.2 := (Option.mem_some_iff.mp ht).symm
        rw [hw2, ← hw1]
        exact (henum w).mpr ⟨t, het⟩
      · simp at ht
  refine ⟨fun a ↦ Nat.rfindOpt (test a), PartrecIn.rfindOpt htest, fun a ↦ ?_, fun a b hb ↦ ?_⟩
  · rw [Nat.rfindOpt_dom]
    constructor
    · rintro ⟨t, b, hb⟩
      exact ⟨b, hsound a b t hb⟩
    · rintro ⟨b, hb⟩
      obtain ⟨t, ht⟩ := (henum (a, b)).mp hb
      exact ⟨t, b, by simp [test, ht]⟩
  · obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hb
    exact hsound a b t ht

/-- Relative enumerability admits relatively computable choice: when every index has a
witness, a dovetailed search along an enumeration finds one, uniformly in the index. -/
theorem IsREIn.exists_computableIn_choice {α β : Type*} [Primcodable α] [Primcodable β]
    {G : α × β → Prop} (hG : IsREIn A G) (htot : ∀ a, ∃ b, G (a, b)) :
    ∃ g : α → β, ComputableIn {charOracle A} g ∧ ∀ a, G (a, g a) := by
  obtain ⟨g, hg, hdom, hsound⟩ := hG.exists_partrecIn_choice
  have hdom' : ∀ a, (g a).Dom := fun a ↦ (hdom a).mpr (htot a)
  exact ⟨fun a ↦ (g a).get (hdom' a),
    PartrecIn.of_eq_tot hg fun a ↦ Part.get_mem (hdom' a),
    fun a ↦ hsound a _ (Part.get_mem (hdom' a))⟩

end Kolmogorov.PointToSet
