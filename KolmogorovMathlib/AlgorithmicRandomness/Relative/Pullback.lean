/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Defs

/-!
# Pulling relatively effective open families back along cylinder maps

If `g : CantorSeq → CantorSeq` is a map whose preimage of every cylinder is a union of cylinders
enumerated computably from the string, then the preimage under `g` of a family that is uniformly
effectively open relative to an oracle `A` is again uniformly effectively open relative to `A`.
This is the relativized form of `isUniformlyEffectiveOpen_pullback`
(`AlgorithmicRandomness/RandomnessConservation.lean`), with the single cylinder there replaced by a
computably enumerated union. The main instance is precomposition `z ↦ z ∘ π` with a primitive
recursive `π : ℕ → ℕ`, which covers the coordinate maps of the van Lambalgen theorem (the even
part of a sequence, the exchange of even and odd positions).

## Conventions

The cylinders covering `g⁻¹(cantorCylinder τ)` are given by `φ τ : ℕ → Option BitString`, with
`none` contributing nothing, as in `IsUniformlyEffectiveOpenIn`. The enumeration of the pulled-back
family at level `n` and stage `i` reads the stage `i.unpair.1` of the original family and the
index `i.unpair.2` of the cover. The cover map `φ` is computable without an oracle; only the
original family uses `A`.

## Main declarations

* `IsUniformlyEffectiveOpenIn.measurableSet`: every member of a uniformly effectively open family
  relative to `A` is measurable.
* `IsUniformlyEffectiveOpenIn.preimage`: pulling back along a map whose cylinder preimages are
  computably enumerated unions of cylinders preserves uniform effective openness relative to `A`.
* `IsUniformlyEffectiveOpenIn.preimage_precomp`: the same for precomposition `z ↦ z ∘ π` with a
  primitive recursive `π`.

Used by `AlgorithmicRandomness/VanLambalgen/Join.lean`,
`AlgorithmicRandomness/VanLambalgen/Directions/` and
`AlgorithmicRandomness/VanLambalgen/Countable/Split.lean`.
-/

namespace Kolmogorov

open MeasureTheory Encodable

variable {A : Set ℕ} {U : ℕ → Set CantorSeq}

/-! ### Measurability and the general pullback -/

/-- Every member of a uniformly effectively open family relative to an oracle is measurable: it is
a countable union of cylinders. -/
theorem IsUniformlyEffectiveOpenIn.measurableSet (hU : IsUniformlyEffectiveOpenIn A U) (n : ℕ) :
    MeasurableSet (U n) := by
  obtain ⟨f, -, hf⟩ := hU
  rw [hf n]
  refine MeasurableSet.iUnion fun i => ?_
  cases f n i
  · exact MeasurableSet.empty
  · exact measurableSet_cantorCylinder _

/-- Pulling a family that is uniformly effectively open relative to `A` back along a map `g`
yields a family that is uniformly effectively open relative to `A`, provided the preimage under
`g` of each cylinder `cantorCylinder τ` is the union of the cylinders enumerated by `φ τ`, for a
computable `φ`. -/
theorem IsUniformlyEffectiveOpenIn.preimage (hU : IsUniformlyEffectiveOpenIn A U)
    {g : CantorSeq → CantorSeq} {φ : BitString → ℕ → Option BitString} (hφ : Computable₂ φ)
    (hg : ∀ τ, g ⁻¹' cantorCylinder τ = ⋃ k, (φ τ k).elim ∅ cantorCylinder) :
    IsUniformlyEffectiveOpenIn A fun n => g ⁻¹' U n := by
  obtain ⟨f, hf, hfU⟩ := hU
  have hP : Computable fun q : Option BitString × ℕ => q.1.bind fun τ => φ τ q.2 :=
    Computable.option_bind Computable.fst
      (hφ.comp Computable.snd (Computable.snd.comp Computable.fst))
  have hj : Computable fun p : ℕ × ℕ => p.2.unpair.1 :=
    Computable.fst.comp (Computable.unpair.comp Computable.snd)
  have hk : Computable fun p : ℕ × ℕ => p.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp Computable.snd)
  refine ⟨fun n i => (f n i.unpair.1).bind fun τ => φ τ i.unpair.2,
    hP.computableIn.comp ((hf.comp ComputableIn.fst hj.computableIn).pair hk.computableIn),
    fun n => ?_⟩
  dsimp only
  rw [hfU n, Set.preimage_iUnion]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j, hz⟩
    cases h : f n j with
    | none => simp [h] at hz
    | some τ =>
      rw [h, Option.elim_some, hg τ, Set.mem_iUnion] at hz
      obtain ⟨k, hk⟩ := hz
      exact ⟨Nat.pair j k, by simpa [h] using hk⟩
  · rintro ⟨i, hz⟩
    cases h : f n i.unpair.1 with
    | none => simp [h] at hz
    | some τ =>
      refine ⟨i.unpair.1, ?_⟩
      rw [h, Option.elim_some, hg τ, Set.mem_iUnion]
      exact ⟨i.unpair.2, by simpa [h] using hz⟩

/-! ### Precomposition with a primitive recursive index map -/

/-- The cover of the preimage of `cantorCylinder τ` under `z ↦ z ∘ π`: the `k`-th entry is the
string `u` decoded from `k`, kept when `u` has the bit `τ[j]` at position `π j` for every
`j < |τ|`, and `none` otherwise. -/
private def precompCover (π : ℕ → ℕ) (τ : BitString) (k : ℕ) : Option BitString :=
  (decode k : Option BitString).bind fun u =>
    if (List.range τ.length).map (fun j => u[π j]?) = τ.map some then some u else none

private lemma primrec_precompCover {π : ℕ → ℕ} (hπ : Primrec π) :
    Primrec₂ (precompCover π) := by
  have hc : PrimrecPred fun q : (BitString × ℕ) × BitString =>
      (List.range q.1.1.length).map (fun j => q.2[π j]?) = q.1.1.map some :=
    PrimrecRel.comp Primrec.eq
      (Primrec.list_map
        (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) (hπ.comp Primrec.snd)))
      (Primrec.list_map (Primrec.fst.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd))
  exact Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (Primrec.ite hc (Primrec.option_some.comp Primrec.snd) (Primrec.const none))

private lemma preimage_precomp_cantorCylinder (π : ℕ → ℕ) (τ : BitString) :
    (fun z : CantorSeq => z ∘ π) ⁻¹' cantorCylinder τ =
      ⋃ k, (precompCover π τ k).elim ∅ cantorCylinder := by
  ext z
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · intro hz
    have hz' : ∀ j (hj : j < τ.length), z (π j) = τ[j] := hz
    have hM : ∀ j < τ.length, π j < ∑ i ∈ Finset.range τ.length, (π i + 1) := fun j hj =>
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Finset.single_le_sum (f := fun i => π i + 1) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hj))
    set u := cantorPrefix z (∑ i ∈ Finset.range τ.length, (π i + 1))
    have hcheck : (List.range τ.length).map (fun j => u[π j]?) = τ.map some := by
      refine List.ext_getElem (by simp) fun j h1 _ => ?_
      have hj : j < τ.length := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getElem?_eq_getElem (by simpa [u] using hM j hj), cantorPrefix_getElem]
      exact congrArg some (hz' j hj)
    refine ⟨encode u, ?_⟩
    simp only [precompCover, encodek, Option.bind_some, hcheck, ↓reduceIte, Option.elim_some]
    intro i hi
    exact (cantorPrefix_getElem z _ i hi).symm
  · rintro ⟨k, hk⟩
    simp only [precompCover] at hk
    cases hd : (decode k : Option BitString) with
    | none => simp [hd] at hk
    | some u =>
      simp only [hd, Option.bind_some] at hk
      split_ifs at hk with hc
      · simp only [Option.elim_some] at hk
        intro j hj
        have h := List.getElem_of_eq hc (by simpa using hj)
        simp only [List.getElem_map, List.getElem_range] at h
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
        exact (hk (π j) hlt).trans heq
      · simp at hk

/-- Precomposition with a primitive recursive index map `π` preserves uniform effective openness
relative to `A`: the preimage of a cylinder under `z ↦ z ∘ π` is the union of the cylinders of
the strings that carry the prescribed bits at the positions `π j`. -/
theorem IsUniformlyEffectiveOpenIn.preimage_precomp (hU : IsUniformlyEffectiveOpenIn A U)
    {π : ℕ → ℕ} (hπ : Primrec π) :
    IsUniformlyEffectiveOpenIn A fun n => (fun z : CantorSeq => z ∘ π) ⁻¹' U n :=
  hU.preimage (primrec_precompCover hπ).to_comp (preimage_precomp_cantorCylinder π)

end Kolmogorov
