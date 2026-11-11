/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Point
import KolmogorovMathlib.PointToSet.SplitPrecision.Normalized
import KolmogorovMathlib.Oracle.PrefixComplexity.SymmetryLower

/-!
# Mutual information of two points at split precisions

For points `x`, `y` of presented metric spaces `P`, `Q` and an oracle `A`, this file defines,
without any hypothesis,

* `splitMutualInfo P Q A x y r s`, the mutual information `I_{r,s}(x : y)` of `x` and `y` at the
  precisions `(r, s)`: the least `A`-mutual information of a pair of ideal points of the balls
  `B(x, 2⁻ʳ)` and `B(y, 2⁻ˢ)` (Definition 1.1 of the notes);
* `minimizerMutualInfo P Q A x y r s`, the version `J_{r,s}(x : y)` over `K`-minimizers of the
  two balls (Notation 1.2);
* `jointPrecisionComplexity P Q A x y r s`, the joint precision complexity `K_{r,s}(x, y)`.

Given precision nets for `P` and `Q` and linear growth at `x` and `y` (the lower direction of
symmetry of information holds for every oracle, `oracleSymmetryLower`), the point families of
`KolmogorovMathlib.PointToSet.SplitPrecision.Point` turn the located-family theorems into:

* `minimizerMutualInfo_le_splitMutualInfo_add` (**Theorem 1.8**): `J = I + O(log r) + O(log s)`;
* `splitMutualInfo_symmetry` (**Theorem 4.4** for two points):
  `I_{r,s}(x : y) = K_r(x) + K_s(y) - K_{r,s}(x, y) + O(log r) + O(log s)`;
* `splitMutualInfo_comm_le` (**Corollary 4.5**): `I(x : y) = I(y : x) + O(1)`;
* the normalized forms along log-comparably divergent precisions
  (`tendsto_minimizerMutualInfo_sub_splitMutualInfo_div`, **Corollary 1.11**, and
  `tendsto_splitMutualInfo_sub_symmetry_div`, **Corollary 6.2**).

Blueprint nodes `split:point-definition`, `split:point-comparison`, `split:point-symmetry`,
`split:point-normalized`.
-/

namespace Kolmogorov.PointToSet

open Filter Topology

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable (P : Presentation X) (Q : Presentation Y) (A : Set ℕ) (x : X) (y : Y)

/-! ### Definitions -/

/-- `K`-minimizers of the ball `B(x, 2⁻ʳ)` among ideal points. Blueprint node
`split:point-definition`. -/
def IsBallMinimizer (r : ℕ) (i : ℕ) : Prop :=
  dist (P.ι i) x < dyadicRadius r ∧
    oracleNatComplexity A i = precisionComplexityNat P A x (dyadicRadius r)

/-- **Mutual information at split precisions** `I_{r,s}(x : y)` (Definition 1.1 of the notes).
Blueprint node `split:point-definition`. -/
noncomputable def splitMutualInfo (r s : ℕ) : ℤ :=
  sInf {I | ∃ i j : ℕ, dist (P.ι i) x < dyadicRadius r ∧ dist (Q.ι j) y < dyadicRadius s ∧
    I = oracleMutualInfo A (natBits i) (natBits j)}

/-- The minimizer version `J_{r,s}(x : y)` (Notation 1.2 of the notes).
Blueprint node `split:point-definition`. -/
noncomputable def minimizerMutualInfo (r s : ℕ) : ℤ :=
  sInf {I | ∃ i j : ℕ, IsBallMinimizer P A x r i ∧ IsBallMinimizer Q A y s j ∧
    I = oracleMutualInfo A (natBits i) (natBits j)}

/-- The **joint precision complexity** `K_{r,s}(x, y)`: the least complexity of a pair code of
ideal points of the two balls. Blueprint node `split:point-definition`. -/
noncomputable def jointPrecisionComplexity (r s : ℕ) : ℕ :=
  minComplexity A {w | ∃ i j : ℕ, dist (P.ι i) x < dyadicRadius r ∧
    dist (Q.ι j) y < dyadicRadius s ∧ w = pairCode (natBits i) (natBits j)}

/-! ### Identification with the located families -/

variable {P Q A x y}

/-- The split mutual information of two points is that of their point families. -/
theorem splitMutualInfo_eq (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x) (hy : HasLinearGrowth Q A y) (r s : ℕ) :
    splitMutualInfo P Q A x y r s =
      (pointFamily hA N hx).splitInfo (pointFamily hA N' hy) r s := by
  unfold splitMutualInfo LocatedFamily.splitInfo LocatedFamily.infoSet
  congr 1
  ext I
  constructor
  · rintro ⟨i, j, hi, hj, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨i, j, hi, hj, rfl⟩

/-- The minimizer mutual information of two points is that of their point families. -/
theorem minimizerMutualInfo_eq (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x) (hy : HasLinearGrowth Q A y) (r s : ℕ) :
    minimizerMutualInfo P Q A x y r s =
      (pointFamily hA N hx).minInfo (pointFamily hA N' hy) r s := by
  unfold minimizerMutualInfo LocatedFamily.minInfo LocatedFamily.minInfoSet
  congr 1
  ext I
  constructor
  · rintro ⟨i, j, hi, hj, rfl⟩
    exact ⟨_, (isMinName_ballNames_iff P A x r i).mpr hi, _,
      (isMinName_ballNames_iff Q A y s j).mpr hj, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨i, -, rfl⟩ := hp.1
    obtain ⟨j, -, rfl⟩ := hq.1
    exact ⟨i, j, (isMinName_ballNames_iff P A x r i).mp hp,
      (isMinName_ballNames_iff Q A y s j).mp hq, rfl⟩

/-- The joint precision complexity of two points is the complexity of the product of their
point families. -/
theorem jointPrecisionComplexity_eq (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x) (hy : HasLinearGrowth Q A y) (r s : ℕ) :
    jointPrecisionComplexity P Q A x y r s =
      ((pointFamily hA N hx).prod hA (pointFamily hA N' hy)).complexity (r, s) := by
  unfold jointPrecisionComplexity LocatedFamily.complexity
  congr 1
  ext w
  constructor
  · rintro ⟨i, j, hi, hj, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨i, j, hi, hj, rfl⟩

/-! ### Elementary facts -/

variable (P Q A x y)

/-- Minimizers of the ball exist. -/
theorem exists_isBallMinimizer (r : ℕ) : ∃ i, IsBallMinimizer P A x r i := by
  obtain ⟨i, hi, heq⟩ := exists_precisionComplexityNat_eq P A x r
  exact ⟨i, hi, heq.symm⟩

/-- `I_{r,s}(x : y) ≤ J_{r,s}(x : y)`: minimizers are ideal points of the balls (inequality (1)
of the notes). Blueprint node `split:point-definition`. -/
theorem splitMutualInfo_le_minimizerMutualInfo (r s : ℕ) :
    splitMutualInfo P Q A x y r s ≤ minimizerMutualInfo P Q A x y r s := by
  obtain ⟨c, hc⟩ := neg_le_oracleMutualInfo A
  obtain ⟨i, hi⟩ := exists_isBallMinimizer P A x r
  obtain ⟨j, hj⟩ := exists_isBallMinimizer Q A y s
  unfold splitMutualInfo minimizerMutualInfo
  apply csInf_le_csInf
  · refine ⟨-(c : ℤ), ?_⟩
    rintro _ ⟨i, j, -, -, rfl⟩
    exact hc _ _
  · exact ⟨oracleMutualInfo A (natBits i) (natBits j), i, j, hi, hj, rfl⟩
  · rintro _ ⟨i, j, hi, hj, rfl⟩
    exact ⟨i, j, hi.1, hj.1, rfl⟩

/-- The split mutual information is attained by a pair of ideal points. -/
theorem exists_splitMutualInfo_eq (r s : ℕ) :
    ∃ i j : ℕ, dist (P.ι i) x < dyadicRadius r ∧ dist (Q.ι j) y < dyadicRadius s ∧
      splitMutualInfo P Q A x y r s = oracleMutualInfo A (natBits i) (natBits j) := by
  obtain ⟨c, hc⟩ := neg_le_oracleMutualInfo A
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.dense x _ (dyadicRadius_pos r)
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp Q.dense y _ (dyadicRadius_pos s)
  have hmem : splitMutualInfo P Q A x y r s ∈ {I | ∃ i j : ℕ, dist (P.ι i) x < dyadicRadius r ∧
      dist (Q.ι j) y < dyadicRadius s ∧ I = oracleMutualInfo A (natBits i) (natBits j)} := by
    refine Int.csInf_mem ⟨oracleMutualInfo A (natBits i) (natBits j), i, j, by rwa [dist_comm],
      by rwa [dist_comm], rfl⟩ ⟨-(c : ℤ), ?_⟩
    rintro _ ⟨i, j, -, -, rfl⟩
    exact hc _ _
  exact hmem

/-- **Symmetry** (Corollary 4.5 of the notes): `I_{r,s}(x : y) ≤ I_{s,r}(y : x) + O(1)`.
Blueprint node `split:point-symmetry`. -/
theorem splitMutualInfo_comm_le :
    ∃ c : ℕ, ∀ r s : ℕ, splitMutualInfo P Q A x y r s ≤ splitMutualInfo Q P A y x s r + c := by
  obtain ⟨c, hc⟩ := neg_le_oracleMutualInfo A
  obtain ⟨cS, hS⟩ := oracleMutualInfo_le_symm A
  refine ⟨cS, fun r s => ?_⟩
  obtain ⟨j, i, hj, hi, hI⟩ := exists_splitMutualInfo_eq Q P A y x s r
  rw [hI]
  have h1 : splitMutualInfo P Q A x y r s ≤ oracleMutualInfo A (natBits i) (natBits j) := by
    refine csInf_le ⟨-(c : ℤ), ?_⟩ ⟨i, j, hi, hj, rfl⟩
    rintro _ ⟨i, j, -, -, rfl⟩
    exact hc _ _
  have h2 := hS (natBits i) (natBits j)
  omega

/-! ### The main theorems for two points -/

variable {P Q A x y}

/-- **Comparison theorem** (Theorem 1.8 of the notes): for a point `x` with linear growth in a
space with precision nets and likewise `y`, and every oracle `A`,
`J_{r,s}(x : y) ≤ I_{r,s}(x : y) + O(log r) + O(log s)`; together with
`splitMutualInfo_le_minimizerMutualInfo`, `I = J + O(log r) + O(log s)`.
Blueprint node `split:point-comparison`. -/
theorem minimizerMutualInfo_le_splitMutualInfo_add
    (N : PrecisionNets P A) (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x)
    (hy : HasLinearGrowth Q A y) :
    ∃ c : ℕ, ∀ r s : ℕ,
      minimizerMutualInfo P Q A x y r s ≤
        splitMutualInfo P Q A x y r s + c * ((Nat.bits r).length + (Nat.bits s).length + 1) := by
  have hA := oracleSymmetryLower A
  obtain ⟨c, hc⟩ := (pointFamily hA N hx).minInfo_le_splitInfo_add (pointFamily hA N' hy) hA
  refine ⟨c, fun r s => ?_⟩
  rw [splitMutualInfo_eq hA N N' hx hy, minimizerMutualInfo_eq hA N N' hx hy]
  exact hc r s

/-- **Symmetry of information at split precisions** for two points (Theorem 4.4 of the notes):
`I_{r,s}(x : y) = K_r(x) + K_s(y) - K_{r,s}(x, y) + O(log r) + O(log s)`.
Blueprint node `split:point-symmetry`. -/
theorem splitMutualInfo_symmetry
    (N : PrecisionNets P A) (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x)
    (hy : HasLinearGrowth Q A y) :
    ∃ c : ℕ, ∀ r s : ℕ,
      splitMutualInfo P Q A x y r s ≤
        (precisionComplexityNat P A x (dyadicRadius r) : ℤ) +
          precisionComplexityNat Q A y (dyadicRadius s) - jointPrecisionComplexity P Q A x y r s +
          c * ((Nat.bits r).length + (Nat.bits s).length + 1) ∧
      (precisionComplexityNat P A x (dyadicRadius r) : ℤ) +
          precisionComplexityNat Q A y (dyadicRadius s) - jointPrecisionComplexity P Q A x y r s ≤
        splitMutualInfo P Q A x y r s + c * ((Nat.bits r).length + (Nat.bits s).length + 1) := by
  have hA := oracleSymmetryLower A
  obtain ⟨c, hc⟩ := (pointFamily hA N hx).splitInfo_symmetry (pointFamily hA N' hy) hA
  refine ⟨c, fun r s => ?_⟩
  rw [splitMutualInfo_eq hA N N' hx hy, jointPrecisionComplexity_eq hA N N' hx hy,
    ← pointFamily_complexity hA N hx, ← pointFamily_complexity hA N' hy]
  exact hc r s

/-! ### Normalized forms -/

/-- Along log-comparably divergent precisions the budgets of two point families are negligible
against the first precision. -/
theorem tendsto_bits_div_of_logComparablyDivergent {r s : ℕ → ℕ} (h : LogComparablyDivergent r s) :
    Tendsto (fun k => ((Nat.bits (r k)).length : ℝ) / r k) atTop (𝓝 0) ∧
      Tendsto (fun k => ((Nat.bits (s k)).length : ℝ) / r k) atTop (𝓝 0) := by
  obtain ⟨hr, hs, hsr, -⟩ := h
  have hN : Tendsto (fun k => ((r k : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hr
  exact ⟨tendsto_bits_length_div_of_log_div hN hr (tendsto_log_div_self_nat hr),
    tendsto_bits_length_div_of_log_div hN hs hsr⟩

/-- **Normalized comparison** (Corollary 1.11 of the notes): along log-comparably divergent
precisions, in particular along comparably divergent ones,
`(J_{r_k,s_k} - I_{r_k,s_k}) / r_k → 0`. Blueprint node `split:point-normalized`. -/
theorem tendsto_minimizerMutualInfo_sub_splitMutualInfo_div
    (N : PrecisionNets P A) (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x)
    (hy : HasLinearGrowth Q A y) {r s : ℕ → ℕ} (h : LogComparablyDivergent r s) :
    Tendsto (fun k => ((minimizerMutualInfo P Q A x y (r k) (s k) -
      splitMutualInfo P Q A x y (r k) (s k) : ℤ) : ℝ) / r k) atTop (𝓝 0) := by
  have hA := oracleSymmetryLower A
  obtain ⟨h₁, h₂⟩ := tendsto_bits_div_of_logComparablyDivergent h
  have hN : Tendsto (fun k => ((r k : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp h.1
  have := (pointFamily hA N hx).tendsto_minInfo_sub_splitInfo_div (pointFamily hA N' hy) hA
    (r := r) (s := s) hN h₁ h₂
  refine this.congr' (Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [splitMutualInfo_eq hA N N' hx hy, minimizerMutualInfo_eq hA N N' hx hy]

/-- **Normalized symmetry of information** (Corollary 6.2 of the notes): along log-comparably
divergent precisions,
`(I_{r_k,s_k}(x : y) - (K_{r_k}(x) + K_{s_k}(y) - K_{r_k,s_k}(x, y))) / r_k → 0`.
Blueprint node `split:point-normalized`. -/
theorem tendsto_splitMutualInfo_sub_symmetry_div
    (N : PrecisionNets P A) (N' : PrecisionNets Q A) (hx : HasLinearGrowth P A x)
    (hy : HasLinearGrowth Q A y) {r s : ℕ → ℕ} (h : LogComparablyDivergent r s) :
    Tendsto (fun k => ((splitMutualInfo P Q A x y (r k) (s k) -
      ((precisionComplexityNat P A x (dyadicRadius (r k)) : ℤ) +
        precisionComplexityNat Q A y (dyadicRadius (s k)) -
        jointPrecisionComplexity P Q A x y (r k) (s k)) : ℤ) : ℝ) / r k) atTop (𝓝 0) := by
  have hA := oracleSymmetryLower A
  obtain ⟨h₁, h₂⟩ := tendsto_bits_div_of_logComparablyDivergent h
  have hN : Tendsto (fun k => ((r k : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp h.1
  have := (pointFamily hA N hx).tendsto_splitInfo_sub_symmetry_div (pointFamily hA N' hy) hA
    (r := r) (s := s) hN h₁ h₂
  refine this.congr' (Eventually.of_forall fun k => ?_)
  beta_reduce
  rw [splitMutualInfo_eq hA N N' hx hy, jointPrecisionComplexity_eq hA N N' hx hy,
    ← pointFamily_complexity hA N hx, ← pointFamily_complexity hA N' hy]

end Kolmogorov.PointToSet
