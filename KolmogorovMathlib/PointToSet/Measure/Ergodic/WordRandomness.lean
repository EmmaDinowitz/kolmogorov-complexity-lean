/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ShiftGeneric

/-!
# Randomness and complexity of sequences over a finite alphabet

The symbolic side of the note *Orbit complexity of Martin-Löf random points equals entropy*
works with words and cylinder tests on `ℕ → α`, without a metric presentation of the shift:

* `listCylinder w`: the sequences extending the finite word `w : List α`;
  `wordPrefix ω n = ω↾n` as a list.
* `IsWordTestIn A ν V`: a Martin-Löf test relative to the oracle `A` for the measure `ν`, made of
  cylinders: `V m = ⋃_{w ∈ E_m} [w]` with `(m, w) ↦ [w ∈ E_m]` `A`-c.e. and `ν(V m) ≤ 2^{-m}`;
  `wordRandomPoints A ν` is the set of sequences that pass every such test.
* `IsComputableWordMeasureIn A ν`: the measures `ν[w]` of the cylinders form an `A`-computable
  real family.
* `wordComplexity A ω n = K^A(ω↾n)`, the prefix complexity relative to `A` of the code of the
  word `ω↾n`.

Blueprint node `erg:words`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {α : Type*}

/-- The cylinder `[w]` of the sequences extending a finite word `w`. Blueprint node
`erg:words`. -/
def listCylinder (w : List α) : Set (ℕ → α) :=
  {y | ∀ i (h : i < w.length), y i = w[i]}

/-- The prefix `ω↾n` of length `n`, as a list. Blueprint node `erg:words`. -/
def wordPrefix (ω : ℕ → α) (n : ℕ) : List α :=
  List.ofFn fun i : Fin n ↦ ω i

/-- A sequence lies in the cylinder of each of its prefixes. Blueprint node `erg:words`. -/
theorem mem_listCylinder_wordPrefix (ω : ℕ → α) (n : ℕ) : ω ∈ listCylinder (wordPrefix ω n) := by
  intro i hi
  simp [wordPrefix]

/-- The cylinder of the list `List.ofFn w` is the cylinder `wordCylinder w`.
Blueprint node `erg:words`. -/
theorem listCylinder_ofFn {k : ℕ} (w : Fin k → α) :
    listCylinder (List.ofFn w) = wordCylinder w := by
  ext y
  simp only [listCylinder, wordCylinder, List.length_ofFn, List.getElem_ofFn, mem_ofPred_eq]
  exact ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩

/-- The cylinder of the prefix `ω↾n` is the `PiNat` cylinder of `ω` of length `n`.
Blueprint node `erg:words`. -/
theorem listCylinder_wordPrefix (ω : ℕ → α) (n : ℕ) :
    listCylinder (wordPrefix ω n) = PiNat.cylinder ω n := by
  ext y
  simp [listCylinder, wordPrefix, PiNat.cylinder]

/-- `ω↾(j + 1) = ω₀ :: (σω)↾j`. Blueprint node `erg:words`. -/
theorem wordPrefix_succ (ω : ℕ → α) (j : ℕ) :
    wordPrefix ω (j + 1) = ω 0 :: wordPrefix (shiftMap ω) j := by
  simp [wordPrefix, List.ofFn_succ, shiftMap]

/-- The complement of a cylinder `[w]` is the union of the cylinders of the other words of the
same length. Blueprint node `erg:words`. -/
theorem iUnion_listCylinder_ne_eq_compl (w : List α) :
    ⋃ w' ∈ {w' : List α | w'.length = w.length ∧ w' ≠ w}, listCylinder w' =
      (listCylinder w)ᶜ := by
  ext y
  simp only [mem_compl_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨w', ⟨hlen, hne⟩, hy'⟩ hy
    refine hne (List.ext_getElem hlen fun i hi hi' ↦ ?_)
    exact (hy' i hi).symm.trans (hy i hi')
  · intro hy
    refine ⟨(List.range w.length).map y, ⟨by simp, ?_⟩, fun i hi ↦ by simp⟩
    rintro hw
    refine hy fun i hi ↦ ?_
    rw [← List.getElem_of_eq hw (by simpa using hi), List.getElem_map, List.getElem_range]

/-- Cylinders of finite words are measurable for the product σ-algebra.
Blueprint node `erg:words`. -/
theorem measurableSet_listCylinder [MeasurableSpace α] [MeasurableSingletonClass α]
    (v : List α) : MeasurableSet (listCylinder v) := by
  have : listCylinder v = ⋂ i : Fin v.length, (fun y : ℕ → α ↦ y i) ⁻¹' {v[i]} := by
    ext y; simp [listCylinder, Fin.forall_iff]
  rw [this]
  exact MeasurableSet.iInter fun i ↦ measurable_pi_apply _ (measurableSet_singleton _)

variable [Primcodable α]

/-- A Martin-Löf test relative to `A` for a measure `ν` on `ℕ → α`, made of cylinders.
Blueprint node `erg:words`. -/
def IsWordTestIn [MeasurableSpace (ℕ → α)] (A : Set ℕ) (ν : Measure (ℕ → α))
    (V : ℕ → Set (ℕ → α)) : Prop :=
  ∃ E : ℕ × List α → Prop, IsREIn A E ∧
    (∀ m, V m = ⋃ w ∈ {w | E (m, w)}, listCylinder w) ∧ ∀ m, ν (V m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m

/-- The sequences that are Martin-Löf random for `ν` relative to `A` (they pass every cylinder
test). Blueprint node `erg:words`. -/
def wordRandomPoints [MeasurableSpace (ℕ → α)] (A : Set ℕ) (ν : Measure (ℕ → α)) :
    Set (ℕ → α) :=
  {ω | ∀ V, IsWordTestIn A ν V → ∃ m, ω ∉ V m}

/-- `ν` is `A`-computable on cylinders: `w ↦ ν[w]` is an `A`-computable real family.
Blueprint node `erg:words`. -/
def IsComputableWordMeasureIn [MeasurableSpace (ℕ → α)] (A : Set ℕ) (ν : Measure (ℕ → α)) :
    Prop :=
  IsComputableRealFamilyIn A fun w : List α ↦ (ν (listCylinder w)).toReal

/-- The prefix complexity `K^A(ω↾n)` of the prefix of length `n`, relative to `A`.
Blueprint node `erg:words`. -/
noncomputable def wordComplexity (A : Set ℕ) (ω : ℕ → α) (n : ℕ) : ℕ :=
  oracleNatComplexity A (Encodable.encode (wordPrefix ω n))

/-- A partial `A`-computable map on indices raises the prefix complexity relative to `A` by at
most a constant: `K^A(j) ≤ K^A(m) + c` whenever `j ∈ E m`. Blueprint node `erg:words`. -/
theorem exists_natComplexity_le_of_partrecIn (A : Set ℕ) (E : ℕ →. ℕ)
    (hE : PartrecIn {charOracle A} E) :
    ∃ c : ℕ, ∀ m j, j ∈ E m → oracleNatComplexity A j ≤ oracleNatComplexity A m + c := by
  let F : List BitString →. BitString := fun ws ↦
    (E (decodeBits (ws.getD 0 []))).map natBits
  have hget : Computable (fun ws : List BitString ↦ ws.getD 0 []) :=
    Computable₂.comp (f := fun (l : List BitString) (n : ℕ) ↦ l.getD n [])
      (Primrec.list_getD ([] : BitString)).to_comp Computable.id (Computable.const 0)
  have hF : PartrecIn {charOracle A} F :=
    (hE.comp (decodeBits_computable.comp hget).computableIn).map
      (natBits_computable.comp Computable.snd).computableIn.to₂
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A 1 F hF
  refine ⟨c, fun m j hj ↦ ?_⟩
  have hFout : natBits j ∈ F [natBits m] := by
    simp only [F, List.getD_cons_zero, natBits, decodeBits_natBits]
    exact Part.mem_map _ hj
  have h := hc [natBits m] (natBits j) rfl hFout
  simpa only [oracleNatComplexity, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero] using h

end Kolmogorov.PointToSet
