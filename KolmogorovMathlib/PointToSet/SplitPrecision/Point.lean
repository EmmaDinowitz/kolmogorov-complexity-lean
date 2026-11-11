/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Located
import KolmogorovMathlib.PointToSet.ComputableMetric.StaticDimensions

/-!
# A point of a presented metric space as a located family

The names of a point `x` of a presented space `P` at precision `r` are the codes `natBits i`
of the ideal points `P.ι i` within `dyadicRadius r` of `x` (`ballNames`); its minimizers are
the `K`-minimizers of the ball, whose common complexity is the precision complexity
`precisionComplexityNat P A x (dyadicRadius r)` (`minComplexity_ballNames`).

Two hypotheses make this a located family with budget `(Nat.bits r).length`, the `O(log r)`
of the notes:

* `PrecisionNets P A`: an `A`-computable family of candidates `cand r q j`, `j < bound`, such
  that every ball `B(x, 2⁻ʳ)` contains a *canonical* ideal point which is a candidate of every
  ideal point `q` of the ball.  In `ℝⁿ` the canonical point is the dyadic truncation of `x` and the
  candidates are the nearby dyadic points (`KolmogorovMathlib.PointToSet.SplitPrecision.Euclidean`).
  This is the geometric content of the transfer lemmas: a name of the ball determines the
  canonical point with `O(log r)` bits, and the canonical point determines any minimizer by the
  lower direction of symmetry of information.
* `HasLinearGrowth P A x`: `K_r(x) ≤ C (r + 1)` (Observation 1.6 / 2.3 of the notes), used
  only through the number of bits of `K_r(x)`.

`pointFamily` packages these into a `LocatedFamily A ℕ`.
Blueprint nodes `split:nets`, `split:point-family`, `split:transfer-geometric`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

variable {X : Type*} [MetricSpace X]

/-! ### Arithmetic of binary lengths -/

/-- The binary length of a product is at most the sum of the binary lengths. -/
theorem bits_length_mul_le (a b : ℕ) :
    (Nat.bits (a * b)).length ≤ (Nat.bits a).length + (Nat.bits b).length := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le, pow_add]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  nlinarith [Nat.mul_le_mul ha.le hb.le]

/-- The binary length of a successor grows by at most one. -/
theorem bits_length_succ_le (a : ℕ) : (Nat.bits (a + 1)).length ≤ (Nat.bits a).length + 1 := by
  simp only [Nat.size_eq_bits_len]
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self a
  omega

/-- Binary length is monotone. -/
theorem bits_length_mono {a b : ℕ} (h : a ≤ b) : (Nat.bits a).length ≤ (Nat.bits b).length := by
  simp only [Nat.size_eq_bits_len]
  exact Nat.size_le_size h

/-! ### Names of a point -/

variable (P : Presentation X) (A : Set ℕ) (x : X)

/-- The names of `x` at precision `r`: codes of the ideal points of the ball `B(x, 2⁻ʳ)`.
Blueprint node `split:point-family`. -/
def ballNames (r : ℕ) : Set BitString :=
  natBits '' {i | dist (P.ι i) x < dyadicRadius r}

/-- Every ball contains an ideal point, so every precision has a name. -/
theorem ballNames_nonempty (r : ℕ) : (ballNames P x r).Nonempty := by
  obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.dense x _ (dyadicRadius_pos r)
  exact ⟨natBits i, i, show dist (P.ι i) x < dyadicRadius r by rwa [dist_comm], rfl⟩

/-- The precision complexity is at most the complexity of any ideal point of the ball. -/
theorem precisionComplexityNat_le_of_dist_lt' {δ : ℝ} {q : ℕ} (hq : dist (P.ι q) x < δ) :
    precisionComplexityNat P A x δ ≤ oracleNatComplexity A q := by
  have h : precisionComplexity P A x δ ≤ (oracleNatComplexity A q : ENat) :=
    iInf_le_of_le q (iInf_le _ hq)
  exact ENat.toNat_le_of_le_natCast h

/-- The precision complexity at a dyadic radius is attained by an ideal point of the ball. -/
theorem exists_precisionComplexityNat_eq (r : ℕ) :
    ∃ i, dist (P.ι i) x < dyadicRadius r ∧
      precisionComplexityNat P A x (dyadicRadius r) = oracleNatComplexity A i := by
  obtain ⟨i, hi, heq⟩ := staticPointDimensions_attained P A x _ (dyadicRadius_pos r)
  refine ⟨i, hi, ?_⟩
  unfold precisionComplexityNat
  rw [heq, ENat.toNat_natCast]

/-- The least complexity of a name of the ball is the precision complexity.
Blueprint node `split:point-family`. -/
theorem minComplexity_ballNames (r : ℕ) :
    minComplexity A (ballNames P x r) = precisionComplexityNat P A x (dyadicRadius r) := by
  obtain ⟨i, hi, heq⟩ := exists_precisionComplexityNat_eq P A x r
  apply le_antisymm
  · rw [heq]
    exact minComplexity_le A ⟨i, hi, rfl⟩
  · refine le_csInf ⟨oracleComplexity A (natBits i), natBits i, ⟨i, hi, rfl⟩, rfl⟩ ?_
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact precisionComplexityNat_le_of_dist_lt' P A x hj

/-- Minimizers of the names of the ball are exactly the `K`-minimizers of the ball. -/
theorem isMinName_ballNames_iff (r : ℕ) (p : ℕ) :
    IsMinName A (ballNames P x r) (natBits p) ↔
      dist (P.ι p) x < dyadicRadius r ∧
        oracleNatComplexity A p = precisionComplexityNat P A x (dyadicRadius r) := by
  constructor
  · rintro ⟨⟨p', hp', hpp⟩, hmin⟩
    have hp'eq : p' = p := natBits_injective hpp
    subst hp'eq
    refine ⟨hp', ?_⟩
    have hmin' : IsMinName A (ballNames P x r) (natBits p') := ⟨⟨p', hp', rfl⟩, hmin⟩
    rw [← minComplexity_ballNames P A x r, hmin'.minComplexity_eq]
    rfl
  · rintro ⟨hp, heq⟩
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    change oracleNatComplexity A p ≤ oracleNatComplexity A j
    rw [heq]
    exact precisionComplexityNat_le_of_dist_lt' P A x hj

/-! ### Nets and linear growth -/

/-- **Precision nets**: an `A`-computable family of candidate ideal points `cand r q j`,
`j < bound`, such that every ball `B(x, 2⁻ʳ)` has a canonical ideal point that is among the
candidates of every ideal point of the ball. Blueprint node `split:nets`. -/
structure PrecisionNets where
  /-- The `j`-th candidate computed from a precision and an ideal point. -/
  cand : ℕ → ℕ → ℕ → ℕ
  /-- The candidate function is `A`-computable. -/
  cand_computable : ComputableIn {charOracle A} fun t : ℕ × ℕ × ℕ => cand t.1 t.2.1 t.2.2
  /-- The uniform bound on the number of candidates. -/
  bound : ℕ
  /-- Every ball has a canonical ideal point among the candidates of each of its ideal points. -/
  canonical : ∀ (r : ℕ) (x : X), ∃ d, dist (P.ι d) x < dyadicRadius r ∧
    ∀ q, dist (P.ι q) x < dyadicRadius r → ∃ j < bound, cand r q j = d

/-- **Linear growth** of the precision complexity: `K_r(x) ≤ C (r + 1)`.
Blueprint node `split:point-family`. -/
def HasLinearGrowth : Prop :=
  ∃ C : ℕ, ∀ r : ℕ, precisionComplexityNat P A x (dyadicRadius r) ≤ C * (r + 1)

variable {P A}

/-- From an ideal point of the ball, the canonical point is described by the precision and
its index in the candidate list: `K(d | q) ≤ O(log r)`. Blueprint node
`split:transfer-geometric`. -/
theorem PrecisionNets.canonical_cond_le (N : PrecisionNets P A) :
    ∃ c : ℕ, ∀ (r : ℕ) (x : X), ∃ d, dist (P.ι d) x < dyadicRadius r ∧
      ∀ q, dist (P.ι q) x < dyadicRadius r →
        oraclePrefixComplexityNat A (natBits d) (natBits q) ≤ c * ((Nat.bits r).length + 1) := by
  -- the decoding map: from the context `q` and the pair `⟨r, j⟩`, return `natBits (cand r q j)`
  let F : BitString → BitString → BitString := fun Q E =>
    natBits (N.cand (decodeBits (decodeFirst E)) (decodeBits Q) (decodeBits (decodeSecond E)))
  have hF : ComputableIn {charOracle A} fun q : BitString × BitString => F q.1 q.2 := by
    have hr : ComputableIn {charOracle A} fun q : BitString × BitString =>
        decodeBits (decodeFirst q.2) :=
      (decodeBits_computable.comp decodeFirst_computable).computableIn.comp ComputableIn.snd
    have hq : ComputableIn {charOracle A} fun q : BitString × BitString => decodeBits q.1 :=
      decodeBits_computable.computableIn.comp ComputableIn.fst
    have hidx : ComputableIn {charOracle A} fun q : BitString × BitString =>
        decodeBits (decodeSecond q.2) :=
      (decodeBits_computable.comp decodeSecond_computable).computableIn.comp ComputableIn.snd
    have htuple : ComputableIn {charOracle A} fun q : BitString × BitString =>
        (decodeBits (decodeFirst q.2), decodeBits q.1, decodeBits (decodeSecond q.2)) :=
      hr.pair (hq.pair hidx)
    exact (primrec_natBits.to_comp.computableIn.comp (N.cand_computable.comp htuple)).of_eq
      fun _ => rfl
  obtain ⟨cF, hcF⟩ := oraclePrefixComplexityNat_map_cond_le A F hF
  obtain ⟨cD, hcD⟩ := oraclePrefixComplexityNat_le_oracleComplexity A
  obtain ⟨cP, hcP⟩ := oracleComplexity_pair_le_add A
  obtain ⟨cB, hcB⟩ := oracleNatComplexity_le_bits A
  refine ⟨cF + cD + cP + 2 * cB + 3 * (Nat.bits N.bound).length + 3, fun r x => ?_⟩
  obtain ⟨d, hd, hcand⟩ := N.canonical r x
  refine ⟨d, hd, fun q hq => ?_⟩
  obtain ⟨j, hj, hget⟩ := hcand q hq
  have hFE : F (natBits q) (pairCode (natBits r) (natBits j)) = natBits d := by
    simp only [F, decodeFirst_pairCode, decodeSecond_pairCode, natBits, decodeBits_natBits, hget]
  have h1 := hcF (pairCode (natBits r) (natBits j)) (natBits q)
  rw [hFE] at h1
  have h2 := hcD (pairCode (natBits r) (natBits j)) (natBits q)
  have h3 := hcP (natBits r) (natBits j)
  have h4 := hcB r
  have h5 := hcB j
  have hj' : (Nat.bits j).length ≤ (Nat.bits N.bound).length := bits_length_mono hj.le
  unfold oracleNatComplexity at h4 h5
  nlinarith

/-! ### The point family -/

variable {x}

/-- The number of bits of `K_r(x)` is `O(log r)` under linear growth. -/
theorem HasLinearGrowth.bits_le (hx : HasLinearGrowth P A x) :
    ∃ c : ℕ, ∀ r : ℕ,
      (Nat.bits (precisionComplexityNat P A x (dyadicRadius r))).length ≤
        c * ((Nat.bits r).length + 1) := by
  obtain ⟨C, hC⟩ := hx
  refine ⟨(Nat.bits C).length + 1, fun r => ?_⟩
  have h1 := bits_length_mono (hC r)
  have h2 := bits_length_mul_le C (r + 1)
  have h3 := bits_length_succ_le r
  nlinarith

/-- **Geometric transfer**: for a point with linear growth in a space with precision nets, every
ideal point of the ball describes every `K`-minimizer of the ball with `O(log r)` bits.
Blueprint node `split:transfer-geometric`. -/
theorem transfer_ballNames (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (hx : HasLinearGrowth P A x) :
    ∃ c : ℕ, ∀ r, ∀ q ∈ ballNames P x r, ∀ p, IsMinName A (ballNames P x r) p →
      oraclePrefixComplexityNat A p q ≤ c * ((Nat.bits r).length + 1) := by
  obtain ⟨ca, hca⟩ := N.canonical_cond_le
  obtain ⟨C, hC⟩ := hx
  obtain ⟨cT, hT⟩ := oraclePrefixComplexityNat_triangle A
  obtain ⟨cS, hS⟩ := hA.bound
  obtain ⟨cW, hW⟩ := oracleComplexity_pair_swap_le A
  obtain ⟨cU, hU⟩ := oracleComplexity_pair_le_cond_context A
  obtain ⟨cX, hX⟩ := oraclePrefixComplexityNat_context_le A
  obtain ⟨cC, hCt⟩ := oraclePrefixComplexityNat_le_context_add A
  obtain ⟨cN, hN⟩ := oracleComplexity_natCode_le A
  -- `C' (r + 1)` bounds `K(d)`.
  set C' := C + ca + cT with hC'
  refine ⟨2 * ca + (cS + cW + cU + cX) + 3 * (Nat.bits C').length + 9 + cN + cC + cT,
    fun r q hq p hp => ?_⟩
  obtain ⟨q', hq', rfl⟩ := hq
  obtain ⟨p', hp', rfl⟩ := hp.1
  have hKp : oracleNatComplexity A p' = precisionComplexityNat P A x (dyadicRadius r) :=
    ((isMinName_ballNames_iff P A x r p').mp hp).2
  obtain ⟨d, hd, hdq⟩ := hca r x
  have hdQ := hdq q' hq'
  have hdP := hdq p' hp'
  set L := (Nat.bits r).length with hL
  have hLr : L ≤ r := length_natBits_le r
  -- `K(p) ≤ K(d)`: the canonical point lies in the ball.
  have hPD : oracleNatComplexity A p' ≤ oracleNatComplexity A d := by
    rw [hKp]; exact precisionComplexityNat_le_of_dist_lt' P A x hd
  -- `K(d) ≤ K(p) + K(d | p) + O(1) ≤ C' (r + 1)`.
  have hKD := hT (natBits d) (natBits p') []
  have hKD' : oracleComplexity A (natBits d) ≤ C' * (r + 1) := by
    have h1 := hC r
    have h2 : oracleComplexity A (natBits p') ≤ C * (r + 1) := by
      change oracleNatComplexity A p' ≤ _; rw [hKp]; exact h1
    have h3 : oraclePrefixComplexityNat A (natBits d) (natBits p') ≤ ca * (r + 1) :=
      hdP.trans (Nat.mul_le_mul_left ca (by omega))
    change oraclePrefixComplexityNat A (natBits d) [] ≤ _ at hKD ⊢
    change oraclePrefixComplexityNat A (natBits p') [] ≤ _ at h2
    rw [hC']
    nlinarith
  have hbitsD : (Nat.bits (oracleComplexity A (natBits d))).length ≤
      (Nat.bits C').length + L + 2 := by
    have h1 := bits_length_mono hKD'
    have h2 := bits_length_mul_le C' (r + 1)
    have h3 := bits_length_succ_le r
    omega
  have hNat : oracleComplexity A (natCode (oracleComplexity A (natBits d))) ≤
      3 * ((Nat.bits C').length + L + 2) + cN := by
    have := hN (oracleComplexity A (natBits d))
    omega
  -- `K(p | d, K(d)) ≤ K(d | p) + O(1)` by the lower direction of symmetry of information.
  have hs1 := hS (natBits d) (natBits p')
  have hs2 := hW (natBits p') (natBits d)
  have hs3 := hU (natBits p') (natBits d)
  have hs4 := hX (natBits d) (natBits p') (oracleComplexity A (natBits p'))
  -- `K(p | d) ≤ K(p | d, K(d)) + K(natCode K(d)) + O(1)`.
  have hs5 := hCt (natBits p') (natBits d) (oracleComplexity A (natBits d))
  -- `K(p | q) ≤ K(d | q) + K(p | d) + O(1)`.
  have hs6 := hT (natBits p') (natBits d) (natBits q')
  change oracleComplexity A (natBits p') ≤ oracleComplexity A (natBits d) at hPD
  have hE : oraclePrefixComplexityNat A (natBits p') (natBits q') ≤
      2 * (ca * (L + 1)) + ((cS + cW + cU + cX) + 3 * ((Nat.bits C').length + L + 2) +
        cN + cC + cT) := by
    omega
  refine hE.trans ?_
  nlinarith

/-- **The located family of a point**: names are the codes of the ideal points of the balls
`B(x, 2⁻ʳ)` and the budget at precision `r` is `(Nat.bits r).length`.
Blueprint node `split:point-family`. -/
noncomputable def pointFamily (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (hx : HasLinearGrowth P A x) : LocatedFamily A ℕ where
  names := ballNames P x
  nonempty := ballNames_nonempty P x
  budget r := (Nat.bits r).length
  transfer := transfer_ballNames hA N hx
  bits_le := by
    obtain ⟨c, hc⟩ := hx.bits_le
    refine ⟨c, fun r p hp => ?_⟩
    rw [← hp.minComplexity_eq, minComplexity_ballNames]
    exact hc r

/-- The names of the point family are the ball names. -/
theorem pointFamily_names (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (hx : HasLinearGrowth P A x) (r : ℕ) : (pointFamily hA N hx).names r = ballNames P x r := rfl

/-- The budget of the point family is the binary length of the precision. -/
theorem pointFamily_budget (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (hx : HasLinearGrowth P A x) (r : ℕ) : (pointFamily hA N hx).budget r = (Nat.bits r).length :=
  rfl

/-- The complexity of the point family at precision `r` is the precision complexity `K_r(x)`.
Blueprint node `split:point-family`. -/
theorem pointFamily_complexity (hA : OracleSymmetryLower A) (N : PrecisionNets P A)
    (hx : HasLinearGrowth P A x) (r : ℕ) :
    (pointFamily hA N hx).complexity r = precisionComplexityNat P A x (dyadicRadius r) :=
  minComplexity_ballNames P A x r

end Kolmogorov.PointToSet
