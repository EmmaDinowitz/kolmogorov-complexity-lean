/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.OrbitLowerAux

/-!
# Transport from a finite alphabet to `Fin p`

The word-level results (`BlockCoding`, Hoyrup's theorem in `SymbolicLowerBound`) are stated for
sequences over `Fin p` with the product σ-algebra. Proposition 7.10 of *Entropy of non-invariant
measures and orbit complexity of random points* is stated for an arbitrary finite alphabet `α`
with a first-difference metric `d(x, y) = β^{firstDiff x y}` and a Borel σ-algebra. This module
transports along the coordinatewise bijection `finCode x = e ∘ x`, `e = Fintype.equivFin α`
(computable, since `α` is finite): measurability, word complexity (up to `O(1)` both ways),
shift entropy, genericity, invariance, ergodicity, word randomness and computability of the
cylinder measures.

Blueprint node `erg:prop710`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {α : Type*} [Fintype α] [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)]
  [BorelSpace (ℕ → α)] {β : ℝ}

/-- The coordinatewise recoding `x ↦ e ∘ x` into `ℕ → Fin |α|`. Blueprint node `erg:prop710`. -/
noncomputable def finCode (x : ℕ → α) : ℕ → Fin (Fintype.card α) :=
  fun i ↦ Fintype.equivFin α (x i)

/-! ### Auxiliary facts: cylinders, prefixes, measurability -/

omit [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The preimage under `finCode` of a list cylinder is the cylinder of the decoded list. -/
private lemma finCode_preimage_listCylinder (w : List (Fin (Fintype.card α))) :
    finCode ⁻¹' listCylinder w = listCylinder (w.map (Fintype.equivFin α).symm) := by
  ext x
  simp only [mem_preimage, listCylinder, mem_ofPred_eq, List.length_map, List.getElem_map,
    finCode, ← Equiv.eq_symm_apply]

omit [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The preimage under `finCode` of a word cylinder is the cylinder of the decoded word. -/
private lemma finCode_preimage_wordCylinder {k : ℕ} (w : Fin k → Fin (Fintype.card α)) :
    finCode ⁻¹' wordCylinder w = wordCylinder ((Fintype.equivFin α).symm ∘ w) := by
  ext x
  simp only [mem_preimage, wordCylinder, mem_ofPred_eq, finCode, Function.comp_apply,
    ← Equiv.eq_symm_apply]

omit [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- The prefixes of `finCode x` are the encoded prefixes of `x`. -/
private lemma wordPrefix_finCode (x : ℕ → α) (n : ℕ) :
    wordPrefix (finCode x) n = (wordPrefix x n).map (Fintype.equivFin α) := by
  rw [wordPrefix, wordPrefix, List.map_ofFn]
  rfl

/-- Word cylinders are measurable for the product σ-algebra on `ℕ → Fin p`. -/
private lemma measurableSet_wordCylinder_fin {p k : ℕ} (w : Fin k → Fin p) :
    MeasurableSet (wordCylinder w : Set (ℕ → Fin p)) := by
  rw [← listCylinder_ofFn]
  exact measurableSet_listCylinder _

/-- The shift is measurable for the product σ-algebra on `ℕ → Fin p`. -/
private lemma measurable_shiftMap_fin {p : ℕ} : Measurable (shiftMap : (ℕ → Fin p) → ℕ → Fin p) :=
  measurable_pi_iff.2 fun j ↦ measurable_pi_apply (j + 1)

/-! ### Transport -/

omit [Primcodable α] [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- `finCode` commutes with the shift. Blueprint node `erg:prop710`. -/
theorem finCode_shiftMap (x : ℕ → α) : finCode (shiftMap x) = shiftMap (finCode x) :=
  rfl

omit [Primcodable α] in
/-- `finCode` is measurable from the Borel σ-algebra of a first-difference metric to the product
σ-algebra. Blueprint node `erg:prop710`. -/
theorem measurable_finCode (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) :
    Measurable (finCode : (ℕ → α) → ℕ → Fin (Fintype.card α)) := by
  refine measurable_pi_iff.2 fun i ↦ measurable_to_countable' fun a ↦ ?_
  have h : (fun x : ℕ → α ↦ finCode x i) ⁻¹' {a} = {x | x i = (Fintype.equivFin α).symm a} := by
    ext x
    simp [finCode, ← Equiv.eq_symm_apply]
  rw [h]
  exact (isOpen_setOf_apply_eq hβ hβ₁ hd i _).measurableSet

omit [Primcodable α] in
/-- The image measure of a list cylinder is the measure of the decoded cylinder. -/
private lemma map_finCode_listCylinder (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (ν : Measure (ℕ → α))
    (w : List (Fin (Fintype.card α))) :
    ν.map finCode (listCylinder w) = ν (listCylinder (w.map (Fintype.equivFin α).symm)) := by
  rw [Measure.map_apply (measurable_finCode hβ hβ₁ hd) (measurableSet_listCylinder w),
    finCode_preimage_listCylinder]

omit [Primcodable α] in
/-- The image measure of a word cylinder is the measure of the decoded cylinder. -/
private lemma map_finCode_wordCylinder (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (ν : Measure (ℕ → α))
    {k : ℕ} (w : Fin k → Fin (Fintype.card α)) :
    ν.map finCode (wordCylinder w) = ν (wordCylinder ((Fintype.equivFin α).symm ∘ w)) := by
  rw [Measure.map_apply (measurable_finCode hβ hβ₁ hd) (measurableSet_wordCylinder_fin w),
    finCode_preimage_wordCylinder]

omit [Fintype α] [Primcodable α] in
/-- Applying `List.map` of a function on a finite type is computable. -/
private lemma computable_list_map {γ δ : Type*} [Finite γ] [Primcodable γ] [Primcodable δ]
    (f : γ → δ) : Computable (List.map f) :=
  (Primrec.list_map Primrec.id ((Primrec.dom_finite f).comp Primrec.snd).to₂).to_comp

omit [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] [BorelSpace (ℕ → α)] in
/-- Recoding changes the word complexity by `O(1)` (both directions).
Blueprint node `erg:prop710`. -/
theorem exists_wordComplexity_finCode_le (A : Set ℕ) :
    ∃ c : ℕ, ∀ (x : ℕ → α) n, wordComplexity A (finCode x) n ≤ wordComplexity A x n + c ∧
      wordComplexity A x n ≤ wordComplexity A (finCode x) n + c := by
  obtain ⟨c₁, hc₁⟩ := orbitLower_complexity_map A (computable_list_map (Fintype.equivFin α))
  obtain ⟨c₂, hc₂⟩ :=
    orbitLower_complexity_map A (computable_list_map (Fintype.equivFin α).symm)
  refine ⟨c₁ + c₂, fun x n ↦ ⟨?_, ?_⟩⟩
  · have h := hc₁ (wordPrefix x n)
    rw [← wordPrefix_finCode] at h
    unfold wordComplexity oracleNatComplexity
    omega
  · have h := hc₂ (wordPrefix (finCode x) n)
    have hw : (wordPrefix (finCode x) n).map (Fintype.equivFin α).symm = wordPrefix x n := by
      rw [wordPrefix_finCode, List.map_map, Equiv.symm_comp_self, List.map_id]
    rw [hw] at h
    unfold wordComplexity oracleNatComplexity
    omega

omit [Primcodable α] in
/-- The image measure has the same cylinder measures, hence the same shift entropy.
Blueprint node `erg:prop710`. -/
theorem shiftEntropy_map_finCode (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (ν : Measure (ℕ → α)) :
    shiftEntropy (ν.map finCode) = shiftEntropy ν := by
  have hb : ∀ k, blockEntropy (ν.map finCode) k = blockEntropy ν k := fun k ↦
    Fintype.sum_equiv ((Equiv.refl (Fin k)).arrowCongr (Fintype.equivFin α).symm) _ _
      fun w ↦ by rw [map_finCode_wordCylinder hβ hβ₁ hd]; rfl
  simp only [shiftEntropy, hb]

omit [Primcodable α] in
/-- Genericity is preserved by recoding. Blueprint node `erg:prop710`. -/
theorem isGenericPoint_map_finCode (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {ν : Measure (ℕ → α)}
    {x : ℕ → α} (hx : IsGenericPoint ν x) : IsGenericPoint (ν.map finCode) (finCode x) := by
  intro k w
  have hset : ∀ n : ℕ, {j | j < n ∧ ∀ i : Fin k, finCode x (j + i) = w i} =
      {j | j < n ∧ ∀ i : Fin k, x (j + i) = ((Fintype.equivFin α).symm ∘ w) i} := by
    intro n
    ext j
    simp only [mem_ofPred_eq, finCode, Function.comp_apply, ← Equiv.eq_symm_apply]
  simp_rw [hset, map_finCode_wordCylinder hβ hβ₁ hd]
  exact hx k _

omit [Primcodable α] in
/-- Invariance is preserved by recoding. Blueprint node `erg:prop710`. -/
theorem measurePreserving_map_finCode (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {ν : Measure (ℕ → α)}
    (hν : MeasurePreserving shiftMap ν ν) :
    MeasurePreserving shiftMap (ν.map finCode) (ν.map finCode) :=
  ((measurable_finCode hβ hβ₁ hd).measurePreserving ν).of_semiconj hν finCode_shiftMap
    measurable_shiftMap_fin

omit [Primcodable α] in
/-- Invariance and ergodicity are preserved by recoding. Blueprint node `erg:prop710`. -/
theorem ergodic_map_finCode (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {ν : Measure (ℕ → α)}
    (hν : Ergodic shiftMap ν) : Ergodic shiftMap (ν.map finCode) :=
  ((measurable_finCode hβ hβ₁ hd).measurePreserving ν).ergodic_of_ergodic_semiconj hν
    measurable_shiftMap_fin finCode_shiftMap

/-- Word randomness is preserved by recoding. Blueprint node `erg:prop710`. -/
theorem finCode_mem_wordRandomPoints (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {A : Set ℕ}
    {ν : Measure (ℕ → α)} {x : ℕ → α} (hx : x ∈ wordRandomPoints A ν) :
    finCode x ∈ wordRandomPoints A (ν.map finCode) := by
  rintro V ⟨E, hE, hV, hμ⟩
  set e := Fintype.equivFin α
  have hc : Computable fun q : ℕ × List α ↦ (q.1, q.2.map e) :=
    Computable.fst.pair ((computable_list_map e).comp Computable.snd)
  refine hx (fun m ↦ finCode ⁻¹' V m)
    ⟨fun q ↦ E (q.1, q.2.map e), hE.comp hc.computableIn, fun m ↦ ?_, fun m ↦ ?_⟩
  · change finCode ⁻¹' V m = ⋃ w ∈ {w | E (m, w.map e)}, listCylinder w
    rw [hV m, preimage_iUnion₂]
    ext y
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop, finCode_preimage_listCylinder]
    constructor
    · rintro ⟨w', hw', hy⟩
      refine ⟨w'.map e.symm, ?_, hy⟩
      rwa [List.map_map, Equiv.self_comp_symm, List.map_id]
    · rintro ⟨w, hw, hy⟩
      refine ⟨w.map e, hw, ?_⟩
      rwa [List.map_map, Equiv.symm_comp_self, List.map_id]
  · exact (Measure.le_map_apply (measurable_finCode hβ hβ₁ hd).aemeasurable _).trans (hμ m)

/-- Computability of the cylinder measures is preserved by recoding.
Blueprint node `erg:prop710`. -/
theorem isComputableWordMeasureIn_map_finCode (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) {A : Set ℕ}
    {ν : Measure (ℕ → α)} (hc : IsComputableWordMeasureIn A ν) :
    IsComputableWordMeasureIn A (ν.map finCode) := by
  have h := IsComputableRealFamilyIn.comp A _ hc (List.map (Fintype.equivFin α).symm)
    (computable_list_map _)
  unfold IsComputableWordMeasureIn
  convert h using 1
  funext w
  rw [Function.comp_apply, map_finCode_listCylinder hβ hβ₁ hd]

end Kolmogorov.PointToSet
