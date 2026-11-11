/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Theorems
import KolmogorovMathlib.Encoding.Tuples

/-!
# Tuples of points at split precisions

The notes state their main theorems for `k` points `x₁, …, x_k` observed at the precisions
`r₁, …, r_k` and `m` points `y₁, …, y_m` at `s₁, …, s_m`, with error `∑ O(log rᵢ) + ∑ O(log sⱼ)`.
Here the tuple is built as an iterated product of located families
(`LocatedFamily.pi`): its names are the list codes `listCode [q₁, …, q_k]` of names of the
coordinates and its budget is the sum of the coordinate budgets.  Every theorem about two located
families then applies verbatim, and the coordinatewise iteration of the notes (Lemma 3.5) is the
transfer property of the product.

For tuples of points in presented spaces (`tupleNames`, `tuplePrecisionComplexity`,
`tupleSplitMutualInfo`, `tupleJointComplexity`) this gives the comparison theorem
(`tupleMinimizerMutualInfo_le_tupleSplitMutualInfo_add`, Theorem 4.1) and symmetry of information
at split precisions (`tupleSplitMutualInfo_symmetry`, Theorem 4.4) with error
`O(∑ᵢ log rᵢ + ∑ⱼ log sⱼ)`.  Blueprint nodes `split:pi`, `split:tuple-theorems`.
-/

universe u

namespace Kolmogorov.PointToSet

open scoped BigOperators

namespace LocatedFamily

variable {A : Set ℕ}

/-! ### Reindexing, the empty tuple and iterated products -/

/-- Reindexing a located family along a map of precision types. Blueprint node `split:pi`. -/
def reindex {ι κ : Type*} (L : LocatedFamily A ι) (e : κ → ι) : LocatedFamily A κ where
  names k := L.names (e k)
  nonempty k := L.nonempty (e k)
  budget k := L.budget (e k)
  transfer := by
    obtain ⟨c, hc⟩ := L.transfer
    exact ⟨c, fun k => hc (e k)⟩
  bits_le := by
    obtain ⟨c, hc⟩ := L.bits_le
    exact ⟨c, fun k => hc (e k)⟩

/-- The located family of the empty tuple: the single name `[]`, with budget `0`.
Blueprint node `split:pi`. -/
def unit : LocatedFamily A Unit where
  names _ := {[]}
  nonempty _ := ⟨[], rfl⟩
  budget _ := 0
  transfer := by
    refine ⟨oraclePrefixComplexityNat A [] [], fun _ q hq p hp => ?_⟩
    rw [Set.mem_singleton_iff] at hq
    have hp' : p = [] := Set.mem_singleton_iff.mp hp.1
    subst hq; subst hp'
    simp
  bits_le := by
    refine ⟨(Nat.bits (oracleComplexity A [])).length, fun _ p hp => ?_⟩
    have hp' : p = [] := Set.mem_singleton_iff.mp hp.1
    subst hp'
    simp

/-- The located family of a tuple of located families, by induction on the number of
coordinates: names are list codes of names of the coordinates, budgets add.
Blueprint node `split:pi`. -/
noncomputable def pi (hA : OracleSymmetryLower A) :
    ∀ {k : ℕ} {ι : Fin k → Type u} (_ : ∀ i, LocatedFamily A (ι i)), LocatedFamily A (∀ i, ι i)
  | 0, _, _ => unit.reindex fun _ => ()
  | _ + 1, _, L =>
    ((L 0).prod hA (pi hA fun i => L i.succ)).reindex fun r => (r 0, fun i => r i.succ)

/-- The names of a tuple family are the list codes of tuples of names of the coordinates.
Blueprint node `split:pi`. -/
theorem mem_pi_names (hA : OracleSymmetryLower A) :
    ∀ {k : ℕ} {ι : Fin k → Type u} (L : ∀ i, LocatedFamily A (ι i)) (r : ∀ i, ι i) (w : BitString),
      w ∈ (pi hA L).names r ↔
        ∃ q : ∀ _ : Fin k, BitString, (∀ i, q i ∈ (L i).names (r i)) ∧ w = listCode (List.ofFn q)
  | 0, _, L, r, w => by
    simp only [pi, reindex, unit, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩
    · rintro ⟨q, -, rfl⟩
      simp [listCode]
  | k + 1, ι, L, r, w => by
    simp only [pi, reindex]
    rw [mem_prod_names]
    constructor
    · rintro ⟨q₀, hq₀, w', hw', rfl⟩
      obtain ⟨q', hq', rfl⟩ := (mem_pi_names hA (fun i => L i.succ) (fun i => r i.succ) w').mp hw'
      refine ⟨Fin.cons q₀ q', ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hq₀
        · simpa using hq' j
      · simp [listCode, List.ofFn_succ]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q 0, hq 0, listCode (List.ofFn fun i => q i.succ), ?_, ?_⟩
      · exact (mem_pi_names hA (fun i => L i.succ) (fun i => r i.succ) _).mpr
          ⟨fun i => q i.succ, fun i => hq i.succ, rfl⟩
      · simp [listCode, List.ofFn_succ]

/-- The budget of a tuple family is the sum of the coordinate budgets.
Blueprint node `split:pi`. -/
theorem pi_budget (hA : OracleSymmetryLower A) :
    ∀ {k : ℕ} {ι : Fin k → Type u} (L : ∀ i, LocatedFamily A (ι i)) (r : ∀ i, ι i),
      (pi hA L).budget r = ∑ i, (L i).budget (r i)
  | 0, _, _, _ => by simp [pi, reindex, unit]
  | k + 1, _, L, r => by
    simp only [pi, reindex, prod_budget, Fin.sum_univ_succ]
    rw [pi_budget hA (fun i => L i.succ) (fun i => r i.succ)]

end LocatedFamily

/-! ### Tuples of points -/

section Tuples

variable {k : ℕ} {X : Fin k → Type*} [∀ i, MetricSpace (X i)]
variable (P : ∀ i, Presentation (X i)) (A : Set ℕ) (x : ∀ i, X i)

/-- The names of the tuple `x̄` at the precision vector `r̄`: list codes of tuples of ideal points
of the balls `B(xᵢ, 2^{-rᵢ})`. Blueprint node `split:tuple-theorems`. -/
def tupleNames (r : Fin k → ℕ) : Set BitString :=
  {w | ∃ q : Fin k → ℕ, (∀ i, dist ((P i).ι (q i)) (x i) < dyadicRadius (r i)) ∧
    w = listCode (List.ofFn fun i => natBits (q i))}

/-- The complexity `K_{r̄}(x̄)` of a tuple of points at a vector of precisions (Definition 2.1
of the notes). Blueprint node `split:tuple-theorems`. -/
noncomputable def tuplePrecisionComplexity (r : Fin k → ℕ) : ℕ :=
  minComplexity A (tupleNames P x r)

variable {P A x}

/-- The located family of a tuple of points with linear growth in spaces with precision nets.
Blueprint node `split:tuple-theorems`. -/
noncomputable def tupleFamily (hA : OracleSymmetryLower A) (N : ∀ i, PrecisionNets (P i) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) : LocatedFamily A (Fin k → ℕ) :=
  LocatedFamily.pi hA fun i => pointFamily hA (N i) (hx i)

/-- The names of the tuple family are the tuple names. -/
theorem tupleFamily_names (hA : OracleSymmetryLower A) (N : ∀ i, PrecisionNets (P i) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) (r : Fin k → ℕ) :
    (tupleFamily hA N hx).names r = tupleNames P x r := by
  ext w
  rw [tupleFamily, LocatedFamily.mem_pi_names]
  constructor
  · rintro ⟨q, hq, rfl⟩
    choose j hj using fun i => (hq i : q i ∈ ballNames (P i) (x i) (r i))
    refine ⟨j, fun i => (hj i).1, ?_⟩
    rw [show q = fun i => natBits (j i) from funext fun i => ((hj i).2).symm]
  · rintro ⟨q, hq, rfl⟩
    exact ⟨fun i => natBits (q i), fun i => ⟨q i, hq i, rfl⟩, rfl⟩

/-- The budget of the tuple family is `∑ᵢ (Nat.bits rᵢ).length`. -/
theorem tupleFamily_budget (hA : OracleSymmetryLower A) (N : ∀ i, PrecisionNets (P i) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) (r : Fin k → ℕ) :
    (tupleFamily hA N hx).budget r = ∑ i, (Nat.bits (r i)).length :=
  LocatedFamily.pi_budget hA _ r

/-- The complexity of the tuple family is the tuple precision complexity. -/
theorem tupleFamily_complexity (hA : OracleSymmetryLower A) (N : ∀ i, PrecisionNets (P i) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) (r : Fin k → ℕ) :
    (tupleFamily hA N hx).complexity r = tuplePrecisionComplexity P A x r := by
  unfold LocatedFamily.complexity tuplePrecisionComplexity
  rw [tupleFamily_names]

end Tuples

section TwoTuples

variable {k m : ℕ} {X : Fin k → Type*} [∀ i, MetricSpace (X i)] {Y : Fin m → Type*}
  [∀ j, MetricSpace (Y j)]
variable (P : ∀ i, Presentation (X i)) (Q : ∀ j, Presentation (Y j)) (A : Set ℕ)
  (x : ∀ i, X i) (y : ∀ j, Y j)

/-- **Mutual information of two tuples at split precisions** `I_{r̄,s̄}(x̄ : ȳ)` (Definition 2.4 of
the notes). Blueprint node `split:tuple-theorems`. -/
noncomputable def tupleSplitMutualInfo (r : Fin k → ℕ) (s : Fin m → ℕ) : ℤ :=
  sInf {I | ∃ w₁ ∈ tupleNames P x r, ∃ w₂ ∈ tupleNames Q y s, I = oracleMutualInfo A w₁ w₂}

/-- The minimizer version `J_{r̄,s̄}(x̄ : ȳ)` over joint `K`-minimizers of the two tuples
(Notation 2.5). Blueprint node `split:tuple-theorems`. -/
noncomputable def tupleMinimizerMutualInfo (r : Fin k → ℕ) (s : Fin m → ℕ) : ℤ :=
  sInf {I | ∃ w₁, IsMinName A (tupleNames P x r) w₁ ∧ ∃ w₂, IsMinName A (tupleNames Q y s) w₂ ∧
    I = oracleMutualInfo A w₁ w₂}

/-- The joint complexity `K_{r̄,s̄}(x̄, ȳ)` of the two tuples: least complexity of a pair code of
tuple names. Blueprint node `split:tuple-theorems`. -/
noncomputable def tupleJointComplexity (r : Fin k → ℕ) (s : Fin m → ℕ) : ℕ :=
  minComplexity A {w | ∃ w₁ ∈ tupleNames P x r, ∃ w₂ ∈ tupleNames Q y s, w = pairCode w₁ w₂}

variable {P Q A x y}

/-- The split mutual information of two tuples is that of their tuple families. -/
theorem tupleSplitMutualInfo_eq (hA : OracleSymmetryLower A) (N : ∀ i, PrecisionNets (P i) A)
    (N' : ∀ j, PrecisionNets (Q j) A) (hx : ∀ i, HasLinearGrowth (P i) A (x i))
    (hy : ∀ j, HasLinearGrowth (Q j) A (y j)) (r : Fin k → ℕ) (s : Fin m → ℕ) :
    tupleSplitMutualInfo P Q A x y r s =
      (tupleFamily hA N hx).splitInfo (tupleFamily hA N' hy) r s := by
  unfold tupleSplitMutualInfo LocatedFamily.splitInfo LocatedFamily.infoSet
  rw [tupleFamily_names, tupleFamily_names]

/-- The minimizer mutual information of two tuples is that of their tuple families. -/
theorem tupleMinimizerMutualInfo_eq (hA : OracleSymmetryLower A)
    (N : ∀ i, PrecisionNets (P i) A) (N' : ∀ j, PrecisionNets (Q j) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) (hy : ∀ j, HasLinearGrowth (Q j) A (y j))
    (r : Fin k → ℕ) (s : Fin m → ℕ) :
    tupleMinimizerMutualInfo P Q A x y r s =
      (tupleFamily hA N hx).minInfo (tupleFamily hA N' hy) r s := by
  unfold tupleMinimizerMutualInfo LocatedFamily.minInfo LocatedFamily.minInfoSet
  rw [tupleFamily_names, tupleFamily_names]

/-- The joint complexity of two tuples is the complexity of the product of their tuple
families. -/
theorem tupleJointComplexity_eq (hA : OracleSymmetryLower A) (N : ∀ i, PrecisionNets (P i) A)
    (N' : ∀ j, PrecisionNets (Q j) A) (hx : ∀ i, HasLinearGrowth (P i) A (x i))
    (hy : ∀ j, HasLinearGrowth (Q j) A (y j)) (r : Fin k → ℕ) (s : Fin m → ℕ) :
    tupleJointComplexity P Q A x y r s =
      ((tupleFamily hA N hx).prod hA (tupleFamily hA N' hy)).complexity (r, s) := by
  unfold tupleJointComplexity LocatedFamily.complexity
  congr 1
  ext w
  rw [LocatedFamily.mem_prod_names]
  simp only [tupleFamily_names]
  exact Iff.rfl

/-- **Comparison theorem for tuples** (Theorem 4.1 of the notes):
`J_{r̄,s̄}(x̄ : ȳ) ≤ I_{r̄,s̄}(x̄ : ȳ) + O(∑ᵢ log rᵢ + ∑ⱼ log sⱼ)`.
Blueprint node `split:tuple-theorems`. -/
theorem tupleMinimizerMutualInfo_le_tupleSplitMutualInfo_add
    (N : ∀ i, PrecisionNets (P i) A) (N' : ∀ j, PrecisionNets (Q j) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) (hy : ∀ j, HasLinearGrowth (Q j) A (y j)) :
    ∃ c : ℕ, ∀ (r : Fin k → ℕ) (s : Fin m → ℕ),
      tupleMinimizerMutualInfo P Q A x y r s ≤
        tupleSplitMutualInfo P Q A x y r s +
          c * (∑ i, (Nat.bits (r i)).length + ∑ j, (Nat.bits (s j)).length + 1) := by
  have hA := oracleSymmetryLower A
  obtain ⟨c, hc⟩ := (tupleFamily hA N hx).minInfo_le_splitInfo_add (tupleFamily hA N' hy) hA
  refine ⟨c, fun r s => ?_⟩
  rw [tupleSplitMutualInfo_eq hA N N' hx hy, tupleMinimizerMutualInfo_eq hA N N' hx hy]
  have := hc r s
  rwa [tupleFamily_budget, tupleFamily_budget] at this

/-- **Symmetry of information at split precisions for tuples** (Theorem 4.4 of the notes):
`I_{r̄,s̄}(x̄ : ȳ) = K_{r̄}(x̄) + K_{s̄}(ȳ) - K_{r̄,s̄}(x̄, ȳ) + O(∑ᵢ log rᵢ + ∑ⱼ log sⱼ)`.
Blueprint node `split:tuple-theorems`. -/
theorem tupleSplitMutualInfo_symmetry
    (N : ∀ i, PrecisionNets (P i) A) (N' : ∀ j, PrecisionNets (Q j) A)
    (hx : ∀ i, HasLinearGrowth (P i) A (x i)) (hy : ∀ j, HasLinearGrowth (Q j) A (y j)) :
    ∃ c : ℕ, ∀ (r : Fin k → ℕ) (s : Fin m → ℕ),
      tupleSplitMutualInfo P Q A x y r s ≤
        (tuplePrecisionComplexity P A x r : ℤ) + tuplePrecisionComplexity Q A y s -
          tupleJointComplexity P Q A x y r s +
          c * (∑ i, (Nat.bits (r i)).length + ∑ j, (Nat.bits (s j)).length + 1) ∧
      (tuplePrecisionComplexity P A x r : ℤ) + tuplePrecisionComplexity Q A y s -
          tupleJointComplexity P Q A x y r s ≤
        tupleSplitMutualInfo P Q A x y r s +
          c * (∑ i, (Nat.bits (r i)).length + ∑ j, (Nat.bits (s j)).length + 1) := by
  have hA := oracleSymmetryLower A
  obtain ⟨c, hc⟩ := (tupleFamily hA N hx).splitInfo_symmetry (tupleFamily hA N' hy) hA
  refine ⟨c, fun r s => ?_⟩
  rw [tupleSplitMutualInfo_eq hA N N' hx hy, tupleJointComplexity_eq hA N N' hx hy,
    ← tupleFamily_complexity hA N hx, ← tupleFamily_complexity hA N' hy]
  have := hc r s
  rwa [tupleFamily_budget, tupleFamily_budget] at this

end TwoTuples

end Kolmogorov.PointToSet
