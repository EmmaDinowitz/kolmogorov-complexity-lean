/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Located

/-!
# Mutual information at split precisions for located families

For two located families `L₁`, `L₂` (over precision types `ι₁`, `ι₂`) the mutual information
at the split precisions `(r, s)` is the least mutual information of a pair of names
(`LocatedFamily.splitInfo`), and `LocatedFamily.minInfo` is the same minimum restricted to
pairs of minimizers.  The two precisions never interact in the definitions and the error of
every theorem is a constant multiple of `budget₁ r + budget₂ s + 1`, never a joint term.

* `splitInfo_le_minInfo`: `I ≤ J`, since minimizers are names.
* `minInfo_le_splitInfo_add` (**comparison theorem**, Theorem 1.8 / 4.1 of the notes):
  `J ≤ I + O(budget₁ r + budget₂ s)`.  The proof installs the `x`-minimizer in the charged
  slot of the symmetry-of-information identity by the plain transfer lemma, then transfers the
  `y`-side by the decorated transfer lemma; no step constrains an `r`-object and an `s`-object
  simultaneously.
* `splitInfo_symmetry` (**symmetry of information at split precisions**, Theorem 4.4):
  `I = K₁(r) + K₂(s) - K₁₂(r, s) + O(budget₁ r + budget₂ s)`, where `K₁₂` is the complexity of
  the product family.
* `splitInfo_comm_le`: `I(L₁ : L₂) = I(L₂ : L₁) + O(1)`.

Blueprint nodes `split:definition`, `split:comparison`, `split:symmetry`.
-/

namespace Kolmogorov.PointToSet

namespace LocatedFamily

variable {A : Set ℕ} {ι₁ ι₂ : Type*} (L₁ : LocatedFamily A ι₁) (L₂ : LocatedFamily A ι₂)

/-! ### Definitions -/

/-- The mutual informations of pairs of names at precisions `(r, s)`.
Blueprint node `split:definition`. -/
def infoSet (r : ι₁) (s : ι₂) : Set ℤ :=
  {I | ∃ q₁ ∈ L₁.names r, ∃ q₂ ∈ L₂.names s, I = oracleMutualInfo A q₁ q₂}

/-- The mutual informations of pairs of minimizers at precisions `(r, s)`.
Blueprint node `split:definition`. -/
def minInfoSet (r : ι₁) (s : ι₂) : Set ℤ :=
  {I | ∃ p₁, IsMinName A (L₁.names r) p₁ ∧ ∃ p₂, IsMinName A (L₂.names s) p₂ ∧
    I = oracleMutualInfo A p₁ p₂}

/-- **Mutual information at split precisions** `I_{r,s}`: the least mutual information of a
pair of names. Blueprint node `split:definition`. -/
noncomputable def splitInfo (r : ι₁) (s : ι₂) : ℤ := sInf (L₁.infoSet L₂ r s)

/-- The minimizer version `J_{r,s}`: the least mutual information of a pair of minimizers.
Blueprint node `split:definition`. -/
noncomputable def minInfo (r : ι₁) (s : ι₂) : ℤ := sInf (L₁.minInfoSet L₂ r s)

/-- There is always a pair of names. -/
theorem infoSet_nonempty (r : ι₁) (s : ι₂) : (L₁.infoSet L₂ r s).Nonempty := by
  obtain ⟨q₁, hq₁⟩ := L₁.nonempty r
  obtain ⟨q₂, hq₂⟩ := L₂.nonempty s
  exact ⟨_, q₁, hq₁, q₂, hq₂, rfl⟩

/-- There is always a pair of minimizers. -/
theorem minInfoSet_nonempty (r : ι₁) (s : ι₂) : (L₁.minInfoSet L₂ r s).Nonempty := by
  obtain ⟨p₁, hp₁⟩ := L₁.exists_min r
  obtain ⟨p₂, hp₂⟩ := L₂.exists_min s
  exact ⟨_, p₁, hp₁, p₂, hp₂, rfl⟩

/-- Pairs of minimizers are pairs of names. -/
theorem minInfoSet_subset (r : ι₁) (s : ι₂) : L₁.minInfoSet L₂ r s ⊆ L₁.infoSet L₂ r s := by
  rintro _ ⟨p₁, hp₁, p₂, hp₂, rfl⟩
  exact ⟨p₁, hp₁.1, p₂, hp₂.1, rfl⟩

/-- Mutual informations of pairs of names are bounded below. -/
theorem infoSet_bddBelow (r : ι₁) (s : ι₂) : BddBelow (L₁.infoSet L₂ r s) := by
  obtain ⟨c, hc⟩ := neg_le_oracleMutualInfo A
  refine ⟨-(c : ℤ), ?_⟩
  rintro _ ⟨q₁, -, q₂, -, rfl⟩
  exact hc q₁ q₂

/-- Mutual informations of pairs of minimizers are bounded below. -/
theorem minInfoSet_bddBelow (r : ι₁) (s : ι₂) : BddBelow (L₁.minInfoSet L₂ r s) :=
  (L₁.infoSet_bddBelow L₂ r s).mono (L₁.minInfoSet_subset L₂ r s)

/-- The split mutual information is attained by a pair of names. Blueprint node
`split:definition`. -/
theorem exists_splitInfo_eq (r : ι₁) (s : ι₂) :
    ∃ q₁ ∈ L₁.names r, ∃ q₂ ∈ L₂.names s, L₁.splitInfo L₂ r s = oracleMutualInfo A q₁ q₂ :=
  Int.csInf_mem (L₁.infoSet_nonempty L₂ r s) (L₁.infoSet_bddBelow L₂ r s)

/-- The minimizer mutual information is attained by a pair of minimizers. -/
theorem exists_minInfo_eq (r : ι₁) (s : ι₂) :
    ∃ p₁, IsMinName A (L₁.names r) p₁ ∧ ∃ p₂, IsMinName A (L₂.names s) p₂ ∧
      L₁.minInfo L₂ r s = oracleMutualInfo A p₁ p₂ :=
  Int.csInf_mem (L₁.minInfoSet_nonempty L₂ r s) (L₁.minInfoSet_bddBelow L₂ r s)

/-- The split mutual information is at most that of any pair of names. -/
theorem splitInfo_le {r : ι₁} {s : ι₂} {q₁ q₂ : BitString} (hq₁ : q₁ ∈ L₁.names r)
    (hq₂ : q₂ ∈ L₂.names s) : L₁.splitInfo L₂ r s ≤ oracleMutualInfo A q₁ q₂ :=
  csInf_le (L₁.infoSet_bddBelow L₂ r s) ⟨q₁, hq₁, q₂, hq₂, rfl⟩

/-- The minimizer mutual information is at most that of any pair of minimizers. -/
theorem minInfo_le {r : ι₁} {s : ι₂} {p₁ p₂ : BitString} (hp₁ : IsMinName A (L₁.names r) p₁)
    (hp₂ : IsMinName A (L₂.names s) p₂) : L₁.minInfo L₂ r s ≤ oracleMutualInfo A p₁ p₂ :=
  csInf_le (L₁.minInfoSet_bddBelow L₂ r s) ⟨p₁, hp₁, p₂, hp₂, rfl⟩

/-- Minimizers are names, so `I_{r,s} ≤ J_{r,s}`. Blueprint node `split:definition`. -/
theorem splitInfo_le_minInfo (r : ι₁) (s : ι₂) : L₁.splitInfo L₂ r s ≤ L₁.minInfo L₂ r s :=
  csInf_le_csInf (L₁.infoSet_bddBelow L₂ r s) (L₁.minInfoSet_nonempty L₂ r s)
    (L₁.minInfoSet_subset L₂ r s)

/-! ### The comparison theorem -/

/-- **Comparison theorem** (Theorem 1.8 and Theorem 4.1 of the notes):
`J_{r,s} ≤ I_{r,s} + O(budget₁ r + budget₂ s)`, the error splitting between the two precisions.
Blueprint node `split:comparison`. -/
theorem minInfo_le_splitInfo_add (hA : OracleSymmetryLower A) :
    ∃ c : ℕ, ∀ (r : ι₁) (s : ι₂),
      L₁.minInfo L₂ r s ≤ L₁.splitInfo L₂ r s + c * (L₁.budget r + L₂.budget s + 1) := by
  obtain ⟨cG, hG⟩ := oracleMutualInfo_ge_cond A
  obtain ⟨cL, hL⟩ := oracleMutualInfo_le_cond A hA
  obtain ⟨cS, hS⟩ := oracleMutualInfo_le_symm A
  obtain ⟨cT, hT⟩ := oraclePrefixComplexityNat_triangle A
  obtain ⟨cX, hX⟩ := oraclePrefixComplexityNat_context_le A
  obtain ⟨cC, hC⟩ := oraclePrefixComplexityNat_le_context_add A
  obtain ⟨c₁, hc₁⟩ := L₁.transfer
  obtain ⟨cN₁, hN₁⟩ := L₁.natCode_complexity_le
  obtain ⟨cTC, hTC⟩ := L₂.transfer_context
  refine ⟨(c₁ + cN₁) + cTC + (cG + cL + cT + cX + cC + cS + cG + cL + cS), fun r s => ?_⟩
  obtain ⟨q₁, hq₁, q₂, hq₂, hI⟩ := L₁.exists_splitInfo_eq L₂ r s
  obtain ⟨p₁, hp₁⟩ := L₁.exists_min r
  obtain ⟨p₂, hp₂⟩ := L₂.exists_min s
  have hJ := L₁.minInfo_le L₂ hp₁ hp₂
  rw [hI]
  -- Step 1 (charged to `r`): `I(q₁ : q₂) ≥ I(p₁ : q₂) - O(budget₁ r)`.
  have s1 := hG q₁ q₂
  have s2 := hT q₂ p₁ (prefixComplexityContext q₁ (oracleComplexity A q₁))
  have s3 := hX p₁ q₁ (oracleComplexity A q₁)
  have s4 := hc₁ r q₁ hq₁ p₁ hp₁
  have s5 := hC q₂ p₁ (oracleComplexity A p₁)
  have s6 := hN₁ r p₁ hp₁
  have s7 := hL p₁ q₂
  -- Step 2 (charged to `s`): `I(p₁ : q₂) ≥ I(p₁ : p₂) - O(budget₂ s)`.
  have t1 := hS q₂ p₁
  have t2 := hG q₂ p₁
  have t3 := hTC s q₂ hq₂ p₂ hp₂ p₁
  have t4 := hL p₂ p₁
  have t5 := hS p₁ p₂
  have hb := budget_combine (c₁ + cN₁) cTC (cG + cL + cT + cX + cC + cS + cG + cL + cS)
    (L₁.budget r) (L₂.budget s)
  push_cast at *
  linarith

/-- `I(L₁ : L₂) ≤ I(L₂ : L₁) + O(1)`: mutual information at split precisions is symmetric
up to a constant. Blueprint node `split:symmetry`. -/
theorem splitInfo_comm_le :
    ∃ c : ℕ, ∀ (r : ι₁) (s : ι₂), L₁.splitInfo L₂ r s ≤ L₂.splitInfo L₁ s r + c := by
  obtain ⟨cS, hS⟩ := oracleMutualInfo_le_symm A
  refine ⟨cS, fun r s => ?_⟩
  obtain ⟨q₂, hq₂, q₁, hq₁, hI⟩ := L₂.exists_splitInfo_eq L₁ s r
  rw [hI]
  have := L₁.splitInfo_le L₂ hq₁ hq₂
  have := hS q₁ q₂
  omega

/-! ### Symmetry of information at split precisions -/

/-- **Symmetry of information at split precisions** (Theorem 4.4 of the notes):
`I_{r,s} = K₁(r) + K₂(s) - K₁₂(r, s) + O(budget₁ r + budget₂ s)`, where `K₁₂` is the complexity
of the product family. Blueprint node `split:symmetry`. -/
theorem splitInfo_symmetry (hA : OracleSymmetryLower A) :
    ∃ c : ℕ, ∀ (r : ι₁) (s : ι₂),
      L₁.splitInfo L₂ r s ≤
        (L₁.complexity r : ℤ) + L₂.complexity s - (L₁.prod hA L₂).complexity (r, s) +
          c * (L₁.budget r + L₂.budget s + 1) ∧
      (L₁.complexity r : ℤ) + L₂.complexity s - (L₁.prod hA L₂).complexity (r, s) ≤
        L₁.splitInfo L₂ r s + c * (L₁.budget r + L₂.budget s + 1) := by
  obtain ⟨cJ, hJ⟩ := L₁.minInfo_le_splitInfo_add L₂ hA
  obtain ⟨cM, hM⟩ := complexity_pair_min_le hA L₁ L₂
  refine ⟨cJ + cM, fun r s => ?_⟩
  obtain ⟨p₁, hp₁, p₂, hp₂, hmin⟩ := L₁.exists_minInfo_eq L₂ r s
  have hIJ := L₁.splitInfo_le_minInfo L₂ r s
  have hJI := hJ r s
  have hK₁ := L₁.complexity_eq hp₁
  have hK₂ := L₂.complexity_eq hp₂
  have hpair_ge : (L₁.prod hA L₂).complexity (r, s) ≤ oracleComplexity A (pairCode p₁ p₂) :=
    (L₁.prod hA L₂).complexity_le ⟨p₁, hp₁.1, p₂, hp₂.1, rfl⟩
  have hpair_le := hM r s p₁ p₂ hp₁ hp₂
  unfold oracleMutualInfo at hmin
  rw [hK₁, hK₂]
  have hnn : (0 : ℤ) ≤ (cJ : ℤ) * (L₁.budget r + L₂.budget s + 1) := by positivity
  have hnn' : (0 : ℤ) ≤ (cM : ℤ) * (L₁.budget r + L₂.budget s + 1) := by positivity
  push_cast at *
  constructor <;> linarith

end LocatedFamily

end Kolmogorov.PointToSet
