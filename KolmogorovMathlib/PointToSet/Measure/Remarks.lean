/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.ExampleFiveFive
import KolmogorovMathlib.PointToSet.Measure.UniversalMeasure

/-!
# Remarks 3.5, 4.4, 6.13, 6.15, 7.2 and 7.9

Formal statements of six remarks of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*. All of them follow from the rest of the chapter.

* **Remark 3.5** (measures the oracle does not compute). The lower bound
  `h_μ ≤ K^A` at the points random relative to a stronger admissible oracle is
  `localEntropy_le_orbitComplexities_of_mem_randomPoints` (`EntropyLaw.lean`). The upper bound
  can fail: `mem_randomPoints_dirac` (`y` is `δ_y`-random relative to every oracle),
  `localEntropy_dirac` (`Φ_{δ_y}(y) = (0, 0)`), and on Cantor space with the shift, for every
  presentation and every oracle `A`, a point `y` with `K̲^A(y, σ) ≥ 1`
  (`exists_dirac_orbitComplexities_not_le`).
* **Remark 4.4** (why Theorem 4.3(a) needs no stronger oracle).
  `exists_countable_null_ceClosed_cover`: the exceptional set
  `{x | ess sup h̲_μ < K̲^A(x, T)}` lies in a countable union of `μ`-null `A`-effectively closed
  sets, and this union contains no `A`-random point. The exceptional sets of Theorem 4.3(b), (c)
  are described through the uniformly `A`-c.e. open sets `cheapBalls`
  (`isCeOpenFamilyIn_cheapBalls_Ici`, `isCeOpenFamilyIn_cheapBalls_singleton`):
  `setOf_frequently_lt_eq_iInter_cheapBalls` and `setOf_lowerOrbitComplexity_lt` (the condition
  "`K_n^A < s'n` for infinitely many `n`" gives countable unions of effective `G_δ` sets),
  `setOf_frequently_le_eq_iInter_iUnion` and `setOf_lt_upperOrbitComplexity` (the condition
  "`K_n^A ≥ s'n` for infinitely many `n`" gives countable unions of countable intersections of
  countable unions of effectively closed sets, one level higher). That Martin-Löf randomness does
  not avoid such null sets in general is `exists_null_upper_exceptional_meets_randomPoints` and
  `exists_null_lower_exceptional_meets_randomPoints`, derived from Example 5.5
  (`ExampleFiveFive.lean`; the witness is Cantor space with its standard presentation
  `cantorPresentation`).
* **Remark 6.13** (reading the earlier results through `m^A`).
  `universalMeasure_bowenBall_ge_measure`:
  `m^A(B_n(x, T, 6ε)) ≥ 2^{-c} μ(B_n(x, T, ε)) / (n² (I_μ + 2)²)`; consequently
  `localEntropy_universalMeasure_le` (`Φ_{m^A} ≤ Φ_μ` everywhere) and
  `localEntropy_universalMeasure_eq_of_mem_randomPoints` (equality at the `μ`-random points).
* **Remark 6.15** (Corollary 6.14 is Theorem 2.1 restricted to admissible oracles).
  `exists_cone_iSup_orbitComplexities_le` (a measure yields oracles computing it with
  `sup_Z K^A ≤ sup_Z h_μ`), `iSup_orbitComplexities_eq_iSup_localEntropy_universalMeasure` (every
  admissible `A` has `sup_Z K^A = sup_Z h_{m^A} ≥ h(Z, T)`), and from these and Corollary 6.14
  `lowerEntropy_eq_iInf_admissible`, `upperEntropy_eq_iInf_admissible`.
* **Remark 7.2** (algorithmic form of the domination lemma).
  `orbitComplexities_eq_localEntropy_le_of_mem_randomPoints`: if `A` is admissible for `μ` and
  `ν`, then `Φ_ν = Ψ^A ≤ Φ_μ` at every point of `R_A^ν`.
* **Remark 7.9** (the gap as an oracle gain). `ae_compProd_orbitComplexities_eq_bind`
  (`Φ_μ(x) = Ψ^A(x)` and `x ∈ R_A^μ` for `M`-a.e. `(ω, x)`), `ae_orbitComplexities_eq_kernel`
  (fibrewise: `Φ_{μ_ω} = Ψ^{A_ω}` on `R_{A_ω}^{μ_ω}`, for each `ω`), and, under a measurability
  hypothesis on `(ω, x) ↦ Ψ^{A_ω}(x)`, the joint statement
  `ae_compProd_orbitComplexities_eq_kernel`, the reading of Theorem 7.3(a) as the monotonicity
  `Ψ^{A_ω} ≤ Ψ^A` (`ae_compProd_orbitComplexities_kernel_le`) and of integral affinity as
  `Ψ^{A_ω} = Ψ^A` almost everywhere (`kernelEntropyLaw_eq_iff_orbitComplexities`). The
  hypothesis holds when `Ω` is countable (`measurable_orbitComplexities_of_countable`) or when
  one oracle serves all components (`measurable_orbitComplexities_const`).

## Divergences from the note

* Remark 7.9 claims that for `M`-almost every `(ω, x)` the point `x` lies in
  `R_A^μ ∩ R_{A_ω}^{μ_ω}`. For an arbitrary choice `ω ↦ A_ω` of oracles the set
  `{(ω, x) | x ∈ R_{A_ω}^{μ_ω}}` need not be measurable, and "for `M`-almost every `(ω, x)`" is
  then not justified by the fibrewise statements. It is stated here fibrewise, and jointly under
  the hypothesis that `(ω, x) ↦ Ψ^{A_ω}(x)` is measurable (true for countable `Ω` and for a
  single oracle).
* Remark 6.13 is stated for an oracle admissible for `μ` (the standing assumption of §3), and
  for every `A`-computable measure of total mass at most one, not only probability measures.

## Not stated

* Remark 4.4: the classification of the exceptional sets in the effective Borel hierarchy
  relative to `A` (`Σ⁰₂(A)`, `Π⁰₂(A)`, `Π⁰₃(A)` classes), and weak 2-randomness. The library has
  `A`-c.e. open sets (`IsCeOpenIn`) but no effective Borel hierarchy relative to an oracle and no
  notion of weak 2-randomness (membership in no `μ`-null `Π⁰₂(A)` class). What is stated instead
  is the explicit description of the exceptional sets as countable unions and intersections of a
  uniformly `A`-c.e. open family and of the complements of its members.
* Remark 6.15: the comparison with Cutler's duality principle and with the results of N. Lutz
  and J. Lutz (commentary).
* Remark 7.2: the sentence on Bernoulli measures (entropy and cross-entropy) is in
  `RemarksRates.lean`.
* Remark 7.9: the reading of Theorem 7.5(b) ("knowing the ergodic component does not compress
  the orbit"), which is commentary on Theorem 7.5(b) itself (proved as
  `ae_compProd_localEntropy_eq_of_ergodicDecomposition`).

Blueprint node `meas:remarks`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ### Remark 3.5 -/

omit [BorelSpace X] in
/-- Remark 3.5: a point `y` is `δ_y`-random relative to every oracle, since a test level of
measure at most `1/2` cannot contain the atom. Blueprint node `meas:remarks`. -/
theorem mem_randomPoints_dirac (P : Presentation X) (B : Set ℕ) (y : X) :
    y ∈ randomPoints P B (Measure.dirac y) := by
  intro U hU
  refine ⟨1, fun hy ↦ ?_⟩
  have h1 := hU.2 1
  rw [Measure.dirac_apply_of_mem hy, pow_one] at h1
  exact absurd h1 (not_le.2 (ENNReal.inv_lt_one.2 ENNReal.one_lt_two))

section cantor

attribute [local instance] cantorMetricSpace

/-- Remark 3.5, the upper bound can fail for a measure the oracle does not compute: on Cantor
space with the shift, for every presentation and every oracle `A` there is a point `y` that is
`δ_y`-random relative to every oracle `B` and has `Φ_{δ_y}(y) = (0, 0)`, while
`K̲^A(y, σ) ≥ 1` and `K̄^A(y, σ) ≥ 1`. So `K^A(y, σ) ≤ h_{δ_y}(σ, y)` fails, in both coordinates.

The note says only that `K̲^A(y, T)` "may be positive"; the point `y` is a fair-coin random point
relative to an oracle above `A` (Theorem 3.3 and `localEntropy_uniformMeasure_shiftMap`).
Blueprint node `meas:remarks`. -/
theorem exists_dirac_orbitComplexities_not_le (P : Presentation (ℕ → Bool)) (A : Set ℕ) :
    ∃ y : ℕ → Bool, (∀ B : Set ℕ, y ∈ randomPoints P B (Measure.dirac y)) ∧
      localEntropy (Measure.dirac y) shiftMap y = (0, 0) ∧
      1 ≤ (orbitComplexities P shiftMap A y).1 ∧ 1 ≤ (orbitComplexities P shiftMap A y).2 := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P shiftMap continuous_shiftMap_cantor
    uniformMeasure
  have hB := hC (oracleJoin A C) (oracle_joins_right A C)
  obtain ⟨y, -, hy⟩ := exists_mem_randomPoints_of_measure_pos P (oracleJoin A C) uniformMeasure
    (Z := univ) (by simp)
  have h := localEntropy_le_orbitComplexities_of_mem_randomPoints P shiftMap
    continuous_shiftMap_cantor (oracle_joins A C) uniformMeasure hB hy
  rw [localEntropy_uniformMeasure_shiftMap] at h
  exact ⟨y, fun B ↦ mem_randomPoints_dirac P B y, localEntropy_dirac _ y, h⟩

end cantor

/-! ### Remark 4.4 -/

/-- The union of the Bowen balls `B_n(x_i, T, 2^{-p})` with `n ∈ S`, `n ≥ 1` and
`K^A(i) < q n`. A point lies in it exactly when `K_n^A(x, T, 2^{-p}) < q n` for some `n ∈ S`,
`n ≥ 1` (`mem_cheapBalls_iff`). Blueprint node `meas:remarks`. -/
def cheapBalls (P : Presentation X) (T : X → X) (A : Set ℕ) (p : ℕ) (q : ℚ) (S : Set ℕ) :
    Set X :=
  ⋃ k ∈ {k : ℕ × ℕ | k.1 ∈ S ∧ 1 ≤ k.1 ∧
      (oracleNatComplexity A k.2 : ℝ) < ((q * k.1 : ℚ) : ℝ)},
    bowenBall T k.1 (P.ι k.2) (dyadicRadius p)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Membership in `cheapBalls`: some `n ∈ S`, `n ≥ 1`, has `K_n^A(x, T, 2^{-p}) < q n`. -/
theorem mem_cheapBalls_iff (P : Presentation X) {T : X → X} (hT : Continuous T) (A : Set ℕ)
    (p : ℕ) (q : ℚ) (S : Set ℕ) (x : X) :
    x ∈ cheapBalls P T A p q S ↔
      ∃ n ∈ S, 1 ≤ n ∧ (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) < q * n := by
  constructor
  · intro hx
    obtain ⟨⟨n, i⟩, ⟨hnS, hn1, hK⟩, hxi⟩ := mem_iUnion₂.1 hx
    refine ⟨n, hnS, hn1, ?_⟩
    have hle : (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) ≤ oracleNatComplexity A i := by
      exact_mod_cast orbitComplexityNat_le_of_mem P T A (mem_bowenBall_symm hxi)
    push_cast at hK
    linarith
  · rintro ⟨n, hnS, hn1, hK⟩
    obtain ⟨i, hi, heq⟩ := entropiesAndOrbitComplexities_attained P T hT A x n hn1 _
      (dyadicRadius_pos p)
    have hKi : orbitComplexityNat P T A x n (dyadicRadius p) = oracleNatComplexity A i := by
      simp [orbitComplexityNat, heq]
    refine mem_iUnion₂.2 ⟨(n, i), ⟨hnS, hn1, ?_⟩, mem_bowenBall_symm hi⟩
    rw [hKi] at hK
    push_cast
    exact hK

omit [MeasurableSpace X] [BorelSpace X] in
/-- `cheapBalls` with the index set cut out by an `A`-r.e. relation `R N n` is `A`-c.e. open,
uniformly in `(p, q, N)`. -/
private lemma isCeOpenFamilyIn_cheapBalls_rel (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T)
    (R : ℕ × ℕ → Prop) (hR : IsREIn A R) :
    IsCeOpenFamilyIn P A fun w : ℕ × ℚ × ℕ ↦ cheapBalls P T A w.1 w.2.1 {n | R (w.2.2, n)} := by
  have hU := isCeOpenFamilyIn_bowenBall P T A hP hTA
  have hg : Computable fun d : ℕ × ℕ × ℕ ↦ (d.2.1, d.2.2, (2 : ℚ)⁻¹ ^ d.1) :=
    (Computable.fst.comp Computable.snd).pair ((Computable.snd.comp Computable.snd).pair
      (computable_pow_half.comp Computable.fst))
  have hV := hU.comp hg
  -- the selecting predicate on `(p, q, N) × (p', n, i)`
  have h₀ : IsREIn A fun v : (ℕ × ℚ × ℕ) × (ℕ × ℕ × ℕ) ↦ v.2.1 = v.1.1 :=
    isREIn_of_computable_decide (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)).decide.to_comp
  have h₁ : IsREIn A fun v : (ℕ × ℚ × ℕ) × (ℕ × ℕ × ℕ) ↦ R (v.1.2.2, v.2.2.1) :=
    hR.comp ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd))).computableIn
  have h₂ : IsREIn A fun v : (ℕ × ℚ × ℕ) × (ℕ × ℕ × ℕ) ↦ 1 ≤ v.2.2.1 :=
    isREIn_of_computable_decide (Primrec.nat_le.comp (Primrec.const 1)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).decide.to_comp
  have hm : Computable fun v : (ℕ × ℚ × ℕ) × (ℕ × ℕ × ℕ) ↦ v.1.2.1 * (v.2.2.1 : ℚ) :=
    computable₂_ratMul.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (ComputableReals.computable_natCastRat.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have h₃ : IsREIn A fun v : (ℕ × ℚ × ℕ) × (ℕ × ℕ × ℕ) ↦
      (oracleNatComplexity A v.2.2.2 : ℝ) < ((v.1.2.1 * v.2.2.1 : ℚ) : ℝ) :=
    (isREIn_oracleNatComplexity_lt A).comp
      (f := fun v : (ℕ × ℚ × ℕ) × (ℕ × ℕ × ℕ) ↦ (v.2.2.2, v.1.2.1 * (v.2.2.1 : ℚ)))
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair hm).computableIn
  obtain ⟨E, hE, hEq⟩ := hV.iUnion_of_isREIn (h₀.and (h₁.and (h₂.and h₃)))
  refine ⟨E, hE, fun w ↦ ?_⟩
  rw [← hEq w]
  ext x
  simp only [cheapBalls, mem_iUnion, mem_ofPred_eq, exists_prop, Prod.exists, cast_inv_two_pow]
  constructor
  · rintro ⟨n, i, ⟨hn, h1, hK⟩, hx⟩
    exact ⟨w.1, n, i, ⟨rfl, hn, h1, hK⟩, hx⟩
  · rintro ⟨p', n, i, ⟨rfl, hn, h1, hK⟩, hx⟩
    exact ⟨n, i, ⟨hn, h1, hK⟩, hx⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- The sets `cheapBalls P T A p q (Ici N)` (some `n ≥ N` has `K_n^A(x, T, 2^{-p}) < q n`) are
`A`-c.e. open, uniformly in `(p, q, N)`. Blueprint node `meas:remarks`. -/
theorem isCeOpenFamilyIn_cheapBalls_Ici (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    IsCeOpenFamilyIn P A fun w : ℕ × ℚ × ℕ ↦ cheapBalls P T A w.1 w.2.1 (Ici w.2.2) :=
  isCeOpenFamilyIn_cheapBalls_rel P T A hP hTA (fun v ↦ v.1 ≤ v.2)
    (isREIn_of_computable_decide Primrec.nat_le.decide.to_comp)

omit [MeasurableSpace X] [BorelSpace X] in
/-- The sets `cheapBalls P T A p q {n}` (`n ≥ 1` and `K_n^A(x, T, 2^{-p}) < q n`) are `A`-c.e.
open, uniformly in `(p, q, n)`. Blueprint node `meas:remarks`. -/
theorem isCeOpenFamilyIn_cheapBalls_singleton (P : Presentation X) (T : X → X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T) :
    IsCeOpenFamilyIn P A fun w : ℕ × ℚ × ℕ ↦ cheapBalls P T A w.1 w.2.1 {w.2.2} := by
  have h := isCeOpenFamilyIn_cheapBalls_rel P T A hP hTA (fun v ↦ v.2 = v.1)
    (isREIn_of_computable_decide (Primrec.eq.comp Primrec.snd Primrec.fst).decide.to_comp)
  exact h

omit [MeasurableSpace X] [BorelSpace X] in
/-- A member of a uniformly `A`-c.e. open family is `A`-c.e. open. -/
private lemma IsCeOpenFamilyIn.isCeOpenIn' {P : Presentation X} {A : Set ℕ} {ι : Type*}
    [Primcodable ι] {U : ι → Set X} (hU : IsCeOpenFamilyIn P A U) (i : ι) :
    IsCeOpenIn P A (U i) := by
  obtain ⟨E, hE, hUE⟩ := hU
  exact ⟨fun b ↦ E (i, b), hE.comp ((Computable.const i).pair Computable.id).computableIn,
    hUE i⟩

/-- `K < q n` in the reals is `K / n < q` in `ℝ≥0∞`, for `n ≥ 1`. -/
private lemma natCast_lt_mul_iff (K : ℕ) {n : ℕ} (hn : 1 ≤ n) (q : ℚ) :
    (K : ℝ) < q * n ↔ (K : ℝ≥0∞) / n < ENNReal.ofReal q := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.one_pos.trans_le hn).ne'
  rw [ENNReal.div_lt_iff (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n)),
    ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul' (Nat.cast_nonneg n),
    ← ENNReal.ofReal_natCast K, ENNReal.ofReal_lt_ofReal_iff']
  constructor
  · intro h
    exact ⟨h, (Nat.cast_nonneg K).trans_lt h⟩
  · exact fun h ↦ h.1

omit [MeasurableSpace X] [BorelSpace X] in
/-- The finite-time rate is `K_n^A / n`. -/
private lemma cost_eq (P : Presentation X) {T : X → X} (hT : Continuous T) (A : Set ℕ) (x : X)
    (p : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    finiteScaleBSCost P T (fun _ ↦ 1) A x n (dyadicRadius p) =
      (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ≥0∞) / n :=
  entropiesAndOrbitComplexities_rate P T hT A x n hn _ (dyadicRadius_pos p)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Remark 4.4, the condition for Theorem 4.3(c): "`K_n^A(x, T, 2^{-p}) < q n` for infinitely
many `n`" defines the intersection of the decreasing sequence of `A`-c.e. open sets
`cheapBalls P T A p q (Ici N)` (uniformly c.e. open in `(p, q, N)` by
`isCeOpenFamilyIn_cheapBalls_Ici`), an effective `G_δ` set. Blueprint node `meas:remarks`. -/
theorem setOf_frequently_lt_eq_iInter_cheapBalls (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (p : ℕ) (q : ℚ) :
    {x | ∃ᶠ n in atTop, (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) < q * n} =
      ⋂ N, cheapBalls P T A p q (Ici N) := by
  ext x
  simp only [mem_ofPred_eq, mem_iInter, mem_cheapBalls_iff P hT, frequently_atTop, mem_Ici]
  constructor
  · intro h N
    obtain ⟨n, hn, hK⟩ := h (max N 1)
    exact ⟨n, le_of_max_le_left hn, le_of_max_le_right hn, hK⟩
  · intro h N
    obtain ⟨n, hnN, -, hK⟩ := h N
    exact ⟨n, hnN, hK⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- Remark 4.4, the exceptional set of Theorem 4.3(c) for the lower complexity: for every
`s`, `{x | K̲^A(x, T) < s}` is the union over rationals `q` with `q < s` of the intersections
over the scales `2^{-p}` of the effective `G_δ` sets
`{x | K_n^A(x, T, 2^{-p}) < q n for infinitely many n}`; a countable union of effective `G_δ`
sets. Blueprint node `meas:remarks`. -/
theorem setOf_lowerOrbitComplexity_lt (P : Presentation X) {T : X → X} (hT : Continuous T)
    (A : Set ℕ) (s : ℝ≥0∞) :
    {x | (orbitComplexities P T A x).1 < s} =
      ⋃ (q : ℚ) (_ : ENNReal.ofReal q < s), ⋂ p : ℕ,
        {x | ∃ᶠ n in atTop, (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) < q * n} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
  rw [orbitComplexities_eq_iSup_orbitComplexityAt]
  constructor
  · intro h
    obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    refine ⟨q, h2, fun p ↦ ?_⟩
    have hp : (orbitComplexityAt P T A x (dyadicRadius p)).1 < ENNReal.ofReal q :=
      (le_iSup (fun p ↦ (orbitComplexityAt P T A x (dyadicRadius p)).1) p).trans_lt h1
    have hfr := frequently_lt_of_liminf_lt (by isBoundedDefault) hp
    refine (hfr.and_eventually (eventually_ge_atTop 1)).mono fun n hn ↦ ?_
    rw [cost_eq P hT A x p hn.2] at hn
    exact (natCast_lt_mul_iff _ hn.2 q).2 hn.1
  · rintro ⟨q, hqs, hq⟩
    refine lt_of_le_of_lt (iSup_le fun p ↦ ?_) hqs
    refine liminf_le_of_frequently_le' (((hq p).and_eventually
      (eventually_ge_atTop 1)).mono fun n hn ↦ ?_)
    rw [cost_eq P hT A x p hn.2]
    exact ((natCast_lt_mul_iff _ hn.2 q).1 hn.1).le

omit [MeasurableSpace X] [BorelSpace X] in
/-- Remark 4.4, the condition for Theorem 4.3(b): "`K_n^A(x, T, 2^{-p}) ≥ q n` for infinitely
many `n`" defines `⋂_N ⋃_{n ≥ N}` of the complements of the `A`-c.e. open sets
`cheapBalls P T A p q {n}` (uniformly c.e. open in `(p, q, n)` by
`isCeOpenFamilyIn_cheapBalls_singleton`): a countable intersection of countable unions of
effectively closed sets, one level above the effective `G_δ` sets.
Blueprint node `meas:remarks`. -/
theorem setOf_frequently_le_eq_iInter_iUnion (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (p : ℕ) (q : ℚ) :
    {x | ∃ᶠ n in atTop, (q : ℝ) * n ≤ orbitComplexityNat P T A x n (dyadicRadius p)} =
      ⋂ N, ⋃ n ∈ Ici N, (cheapBalls P T A p q {n})ᶜ := by
  ext x
  simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_compl_iff, mem_cheapBalls_iff P hT,
    mem_singleton_iff, frequently_atTop, mem_Ici, exists_prop, exists_eq_left, not_and, not_lt]
  constructor
  · intro h N
    obtain ⟨n, hn, hK⟩ := h (max N 1)
    exact ⟨n, le_of_max_le_left hn, fun _ ↦ hK⟩
  · intro h N
    obtain ⟨n, hnN, hK⟩ := h (max N 1)
    exact ⟨n, le_of_max_le_left hnN, hK (le_of_max_le_right hnN)⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- Remark 4.4, the exceptional set of Theorem 4.3(b): for every `s`,
`{x | s < K̄^A(x, T)}` is the union over the scales `2^{-p}` and the rationals `q > s` of the sets
`{x | K_n^A(x, T, 2^{-p}) ≥ q n for infinitely many n}`. Blueprint node `meas:remarks`. -/
theorem setOf_lt_upperOrbitComplexity (P : Presentation X) {T : X → X} (hT : Continuous T)
    (A : Set ℕ) (s : ℝ≥0∞) :
    {x | s < (orbitComplexities P T A x).2} =
      ⋃ (p : ℕ) (q : ℚ) (_ : s < ENNReal.ofReal q),
        {x | ∃ᶠ n in atTop, (q : ℝ) * n ≤ orbitComplexityNat P T A x n (dyadicRadius p)} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [orbitComplexities_eq_iSup_orbitComplexityAt]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := lt_iSup_iff.1 h
    obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hp
    refine ⟨p, q, h1, ?_⟩
    have hfr := frequently_lt_of_lt_limsup (by isBoundedDefault) h2
    refine (hfr.and_eventually (eventually_ge_atTop 1)).mono fun n hn ↦ ?_
    rw [cost_eq P hT A x p hn.2] at hn
    exact not_lt.1 fun hlt ↦ (lt_asymm hn.1) ((natCast_lt_mul_iff _ hn.2 q).1 hlt)
  · rintro ⟨p, q, hqs, hq⟩
    refine hqs.trans_le (le_trans ?_
      (le_iSup (fun p ↦ (orbitComplexityAt P T A x (dyadicRadius p)).2) p))
    refine le_limsup_of_frequently_le' ((hq.and_eventually
      (eventually_ge_atTop 1)).mono fun n hn ↦ ?_)
    rw [cost_eq P hT A x p hn.2]
    exact not_lt.1 fun hlt ↦ (not_lt.2 hn.1) ((natCast_lt_mul_iff _ hn.2 q).2 hlt)

/-- Remark 4.4, first sentence: for an admissible oracle `A`, the exceptional set
`{x | ess sup h̲_μ < K̲^A(x, T)}` of Theorem 4.3(a) lies in the union of a countable family of
`μ`-null `A`-effectively closed sets (sets whose complement is `A`-c.e. open), and this union
contains no point that is `μ`-random relative to `A`. The sets are the complements of
`cheapBalls P T A p q (Ici N)` with `ess sup h̲_μ < q`. Blueprint node `meas:remarks`. -/
theorem exists_countable_null_ceClosed_cover (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    ∃ F : Set (Set X), F.Countable ∧ (∀ E ∈ F, μ E = 0 ∧ IsCeOpenIn P A Eᶜ) ∧
      {x | essSup (fun y ↦ (localEntropy μ T y).1) μ < (orbitComplexities P T A x).1} ⊆
        ⋃₀ F ∧ Disjoint (randomPoints P A μ) (⋃₀ F) := by
  set S := essSup (fun y ↦ (localEntropy μ T y).1) μ with hS
  set F : Set (Set X) := (fun w : ℕ × ℚ × ℕ ↦ (cheapBalls P T A w.1 w.2.1 (Ici w.2.2))ᶜ) ''
    {w | S < ENNReal.ofReal w.2.1} with hF
  -- the exceptional set is null
  have hN : μ {y | ¬ (orbitComplexities P T A y).1 ≤ S} = 0 := by
    rw [← ae_iff]
    filter_upwards [ae_orbitComplexities_eq_localEntropy P T hT A μ hA,
      ENNReal.ae_le_essSup (μ := μ) fun x ↦ (localEntropy μ T x).1] with y hy hyS
    rw [hy]
    exact hyS
  have hmem : ∀ E ∈ F, μ E = 0 ∧ IsCeOpenIn P A Eᶜ := by
    rintro E ⟨⟨p, q, N⟩, hq, rfl⟩
    refine ⟨measure_mono_null (fun y hy ↦ ?_) hN, ?_⟩
    · simp only [mem_compl_iff, mem_cheapBalls_iff P hT, mem_Ici, not_exists, not_and,
        not_lt] at hy
      simp only [mem_ofPred_eq] at hq ⊢
      refine not_le.2 (hq.trans_le (le_trans ?_ (orbitComplexityAt_le_orbitComplexities P T A y
        (dyadicRadius_pos p)).1))
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [eventually_ge_atTop (max N 1)] with n hn
      rw [cost_eq P hT A y p (le_of_max_le_right hn)]
      exact not_lt.1 fun hlt ↦ (not_lt.2 (hy n (le_of_max_le_left hn)
        (le_of_max_le_right hn))) ((natCast_lt_mul_iff _ (le_of_max_le_right hn) q).2 hlt)
    · rw [compl_compl]
      exact (isCeOpenFamilyIn_cheapBalls_Ici P T A hA.1 hA.2.1).isCeOpenIn' (p, q, N)
  refine ⟨F, (to_countable _).image _, hmem, fun x hx ↦ ?_, ?_⟩
  · simp only [mem_ofPred_eq] at hx
    rw [orbitComplexities_eq_iSup_orbitComplexityAt] at hx
    obtain ⟨p, hp⟩ := lt_iSup_iff.1 hx
    obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hp
    by_contra hcon
    have hall : ∀ N, x ∈ cheapBalls P T A p q (Ici N) := fun N ↦ by
      by_contra hxN
      exact hcon ⟨_, ⟨(p, q, N), h1, rfl⟩, hxN⟩
    have hfr : ∃ᶠ n in atTop, (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) < q * n := by
      rw [← mem_ofPred_eq (p := fun x ↦ ∃ᶠ n in atTop,
        (orbitComplexityNat P T A x n (dyadicRadius p) : ℝ) < q * n),
        setOf_frequently_lt_eq_iInter_cheapBalls P hT A p q]
      exact mem_iInter.2 hall
    refine absurd (liminf_le_of_frequently_le' ((hfr.and_eventually
      (eventually_ge_atTop 1)).mono fun n hn ↦ ?_)) (not_le.2 h2)
    rw [cost_eq P hT A x p hn.2]
    exact ((natCast_lt_mul_iff _ hn.2 q).1 hn.1).le
  · rw [disjoint_sUnion_right]
    intro E hE
    obtain ⟨hE0, hEc⟩ := hmem E hE
    rw [← subset_compl_iff_disjoint_right]
    exact randomPoints_subset_of_isCeOpenIn P A μ hA.1 hA.2.2 hEc (by rwa [compl_compl])

/-- The exceptional set of Theorem 4.3(b) is null: `K̄^A(x, T) ≤ ess sup h̄_μ` almost
everywhere, for an admissible `A`. -/
theorem measure_setOf_essSup_lt_upperOrbitComplexity (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    μ {x | essSup (fun y ↦ (localEntropy μ T y).2) μ < (orbitComplexities P T A x).2} = 0 := by
  have h : ∀ᵐ x ∂μ,
      (orbitComplexities P T A x).2 ≤ essSup (fun y ↦ (localEntropy μ T y).2) μ := by
    filter_upwards [ae_orbitComplexities_eq_localEntropy P T hT A μ hA,
      ENNReal.ae_le_essSup (μ := μ) fun x ↦ (localEntropy μ T x).2] with y hy hyS
    rw [hy]
    exact hyS
  rw [ae_iff] at h
  simpa only [not_le] using h

/-- The exceptional set of Theorem 4.3(c) for the lower complexity is null:
`ess inf h̲_μ ≤ K̲^A(x, T)` almost everywhere, for an admissible `A`. -/
theorem measure_setOf_lowerOrbitComplexity_lt_essInf (P : Presentation X) {T : X → X}
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) :
    μ {x | (orbitComplexities P T A x).1 < essInf (fun y ↦ (localEntropy μ T y).1) μ} = 0 := by
  have h : ∀ᵐ x ∂μ,
      essInf (fun y ↦ (localEntropy μ T y).1) μ ≤ (orbitComplexities P T A x).1 := by
    filter_upwards [ae_orbitComplexities_eq_localEntropy P T hT A μ hA,
      ae_essInf_le (μ := μ) (f := fun x ↦ (localEntropy μ T x).1)] with y hy hyS
    rw [hy]
    exact hyS
  rw [ae_iff] at h
  simpa only [not_le] using h

section cantor

attribute [local instance] cantorMetricSpace

/-- Remark 4.4, last sentence, for Theorem 4.3(b): Martin-Löf randomness does not in general
avoid the null exceptional set `{x | ess sup h̄_μ < K̄^A(x, T)}`. On Cantor space with the shift
there are a presentation, a probability measure and an admissible oracle for which this set is
`μ`-null and contains an `A`-random point; the presentation is the standard one,
`cantorPresentation`.

Derived from Example 5.5(1) (`exists_iSup_randomPoints_gt_essSup`, `ExampleFiveFive.lean`).
Blueprint node `meas:remarks`. -/
theorem exists_null_upper_exceptional_meets_randomPoints :
    ∃ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ ∧ IsMeasureAdmissible P shiftMap μ A ∧
      μ {x | essSup (fun y ↦ (localEntropy μ shiftMap y).2) μ <
        (orbitComplexities P shiftMap A x).2} = 0 ∧
      ({x | essSup (fun y ↦ (localEntropy μ shiftMap y).2) μ <
        (orbitComplexities P shiftMap A x).2} ∩ randomPoints P A μ).Nonempty := by
  obtain ⟨μ, A, hμ, hA, hlt⟩ := exists_iSup_randomPoints_gt_essSup
  obtain ⟨x, hx, hxlt⟩ := lt_biSup_iff.1 hlt
  exact ⟨cantorPresentation, μ, A, hμ, hA, measure_setOf_essSup_lt_upperOrbitComplexity
    cantorPresentation continuous_shiftMap_cantor A μ hA, x, hxlt, hx⟩

/-- Remark 4.4, last sentence, for Theorem 4.3(c): Martin-Löf randomness does not in general
avoid the null exceptional set `{x | K̲^A(x, T) < ess inf h̲_μ}`. On Cantor space with the shift
there are a presentation, a probability measure and an admissible oracle for which this set is
`μ`-null and contains an `A`-random point; the presentation is the standard one,
`cantorPresentation`.

Derived from Example 5.5(2) (`exists_iInf_randomPoints_lt_essInf`, `ExampleFiveFive.lean`).
Blueprint node `meas:remarks`. -/
theorem exists_null_lower_exceptional_meets_randomPoints :
    ∃ (P : Presentation (ℕ → Bool)) (μ : Measure (ℕ → Bool)) (A : Set ℕ),
      IsProbabilityMeasure μ ∧ IsMeasureAdmissible P shiftMap μ A ∧
      μ {x | (orbitComplexities P shiftMap A x).1 <
        essInf (fun y ↦ (localEntropy μ shiftMap y).1) μ} = 0 ∧
      ({x | (orbitComplexities P shiftMap A x).1 <
        essInf (fun y ↦ (localEntropy μ shiftMap y).1) μ} ∩ randomPoints P A μ).Nonempty := by
  obtain ⟨μ, A, hμ, hA, hlt⟩ := exists_iInf_randomPoints_lt_essInf
  simp only [iInf_lt_iff] at hlt
  obtain ⟨x, hx, hxlt⟩ := hlt
  exact ⟨cantorPresentation, μ, A, hμ, hA, measure_setOf_lowerOrbitComplexity_lt_essInf
    cantorPresentation continuous_shiftMap_cantor A μ hA, x, hxlt, hx⟩

end cantor

/-! ### Remark 6.13 -/

/-- Remark 6.13: the universal measure dominates every measure computed by `A` on Bowen
balls, up to a subexponential factor and a change of scale. For `A` admissible for a measure
`μ` of total mass at most one and rational `ε > 0` there is `c` with
`m^A(B_n(x, T, 6ε)) ≥ 2^{-c} μ(B_n(x, T, ε)) / (n² (I_μ + 2)²)`,
`I_μ = -log₂ μ(B_n(x, T, ε))`, for every `x` and `n ≥ 1` (both sides as real numbers; when the
ball is `μ`-null the left side is `0`).

The note assumes `μ` `A`-computable; here `A` is admissible for `μ` (the standing assumption of
§3, needed by Lemma 3.1), and `μ` need only have total mass at most one.
Blueprint node `meas:remarks`. -/
theorem universalMeasure_bowenBall_ge_measure (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P T μ A) (ε : ℚ) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ (x : X) (n : ℕ), 1 ≤ n →
      (2 : ℝ) ^ (-(c : ℝ)) * (μ (bowenBall T n x (ε : ℝ))).toReal /
          ((n : ℝ) ^ 2 * (-Real.logb 2 (μ (bowenBall T n x (ε : ℝ))).toReal + 2) ^ 2) ≤
        (universalMeasure P A (bowenBall T n x (6 * (ε : ℝ)))).toReal := by
  obtain ⟨c, hc⟩ := coding_by_measure_info P T hT A μ hμ hA ε hε
  refine ⟨c, fun x n hn ↦ ?_⟩
  by_cases h0 : μ (bowenBall T n x (ε : ℝ)) = 0
  · rw [h0, ENNReal.toReal_zero, mul_zero, zero_div]
    exact ENNReal.toReal_nonneg
  have hK := hc x n hn h0
  set m := (μ (bowenBall T n x (ε : ℝ))).toReal with hm
  have hm_pos : 0 < m := ENNReal.toReal_pos h0 (measure_ne_top μ _)
  have hm_le : m ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top
      ((measure_mono (subset_univ (bowenBall T n x (ε : ℝ)))).trans hμ)
    rwa [ENNReal.toReal_one] at this
  set I := -Real.logb 2 m with hI
  have hI0 : 0 ≤ I := by
    have := Real.logb_nonpos one_lt_two hm_pos.le hm_le
    linarith
  set K := orbitComplexityNat P T A x n (6 * (ε : ℝ)) with hKdef
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `m^A(B_n(x, T, 6ε)) ≥ 2^{-K}`
  have hU : (2 : ℝ) ^ (-(K : ℝ)) ≤
      (universalMeasure P A (bowenBall T n x (6 * (ε : ℝ)))).toReal := by
    have h := universalMeasure_bowenBall_ge P T hT A x hn (ε := 6 * (ε : ℝ))
      (by have : (0 : ℝ) < ε := by exact_mod_cast hε
          linarith)
    have h' := ENNReal.toReal_mono (measure_ne_top _ _) h
    rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
    rwa [Real.rpow_neg zero_le_two, Real.rpow_natCast, ← inv_pow]
  -- the left side is `2^{-(I + 2 log₂ n + 2 log₂ (I + 2) + c)}`
  have hmI : m = (2 : ℝ) ^ (-I) := by
    rw [hI, neg_neg, Real.rpow_logb two_pos (by norm_num) hm_pos]
  have hn2 : (n : ℝ) ^ 2 = (2 : ℝ) ^ (2 * Real.logb 2 n) := by
    rw [mul_comm, Real.rpow_mul zero_le_two, Real.rpow_logb two_pos (by norm_num) hn0,
      Real.rpow_two]
  have hI2 : (I + 2) ^ 2 = (2 : ℝ) ^ (2 * Real.logb 2 (I + 2)) := by
    rw [mul_comm, Real.rpow_mul zero_le_two, Real.rpow_logb two_pos (by norm_num)
      (by linarith), Real.rpow_two]
  have hlhs : (2 : ℝ) ^ (-(c : ℝ)) * m / ((n : ℝ) ^ 2 * (I + 2) ^ 2) =
      (2 : ℝ) ^ (-(I + 2 * Real.logb 2 n + 2 * Real.logb 2 (I + 2) + c)) := by
    rw [hn2, hI2, ← Real.rpow_add two_pos, hmI, ← Real.rpow_add two_pos,
      ← Real.rpow_sub two_pos]
    congr 1
    ring
  rw [hlhs]
  refine le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) hU
  linarith

/-- Remark 6.13, consequence: for `A` admissible for a measure `μ` of total mass at most one,
`Φ_{m^A} ≤ Φ_μ` coordinatewise at every point (Proposition 6.12 and Theorem 3.3(i)).
Blueprint node `meas:remarks`. -/
theorem localEntropy_universalMeasure_le (P : Presentation X) (T : X → X) (hT : Continuous T)
    (A : Set ℕ) (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ univ ≤ 1)
    (hA : IsMeasureAdmissible P T μ A) (x : X) :
    (localEntropy (universalMeasure P A) T x).1 ≤ (localEntropy μ T x).1 ∧
      (localEntropy (universalMeasure P A) T x).2 ≤ (localEntropy μ T x).2 := by
  rw [← orbitComplexities_eq_localEntropy_universalMeasure P T hT A hA.1 hA.2.1 x]
  exact orbitComplexities_le_localEntropy P T hT A μ hμ hA x

/-- Remark 6.13, consequence: for `A` admissible for a Borel probability measure `μ`,
`Φ_{m^A} = Φ_μ` at every point that is `μ`-random relative to `A` (Proposition 6.12 and
Theorem 3.3). Blueprint node `meas:remarks`. -/
theorem localEntropy_universalMeasure_eq_of_mem_randomPoints (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) {x : X} (hx : x ∈ randomPoints P A μ) :
    localEntropy (universalMeasure P A) T x = localEntropy μ T x := by
  rw [← orbitComplexities_eq_localEntropy_universalMeasure P T hT A hA.1 hA.2.1 x,
    orbitComplexities_eq_localEntropy P T hT A μ hA hx]

/-! ### Remark 6.15 -/

/-- Remark 6.15, first half: every Borel probability measure `μ` is computed by all oracles of
an upper cone, and each of them is admissible for `μ` and has
`sup_{x ∈ Z} K̲^A(x, T) ≤ sup_{x ∈ Z} h̲_μ(T, x)` and the same for the upper quantities, for
every `Z`. Blueprint node `meas:remarks`. -/
theorem exists_cone_iSup_orbitComplexities_le (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ C : Set ℕ, ∀ A : Set ℕ, charOracle C ≤ᵀ charOracle A →
      IsMeasureAdmissible P T μ A ∧ ∀ Z : Set X,
        (⨆ x ∈ Z, (orbitComplexities P T A x).1) ≤ ⨆ x ∈ Z, (localEntropy μ T x).1 ∧
        (⨆ x ∈ Z, (orbitComplexities P T A x).2) ≤ ⨆ x ∈ Z, (localEntropy μ T x).2 := by
  obtain ⟨C, hC⟩ := exists_measureAdmissible_base P T hT μ
  refine ⟨C, fun A hCA ↦ ⟨hC A hCA, fun Z ↦ ⟨iSup₂_mono fun x _ ↦ ?_, iSup₂_mono fun x _ ↦ ?_⟩⟩⟩
  · exact (orbitComplexities_le_localEntropy P T hT A μ prob_le_one (hC A hCA) x).1
  · exact (orbitComplexities_le_localEntropy P T hT A μ prob_le_one (hC A hCA) x).2

omit [BorelSpace X] in
/-- The normalized universal measure is a probability measure with the same local entropies. -/
private lemma localEntropy_normalized (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X) :
    IsProbabilityMeasure ((universalMeasure P A univ)⁻¹ • universalMeasure P A) ∧
      localEntropy ((universalMeasure P A univ)⁻¹ • universalMeasure P A) T x =
        localEntropy (universalMeasure P A) T x := by
  have h0 := universalMeasure_univ_ne_zero P A
  have htop := measure_ne_top (universalMeasure P A) univ
  exact ⟨⟨by simp [Measure.smul_apply, ENNReal.inv_mul_cancel h0 htop]⟩,
    localEntropy_smul _ T x (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0)⟩

/-- Remark 6.15, second half: every oracle `A` that computes the metric table and represents
`T` has `sup_{x ∈ Z} K̲^A(x, T) = sup_{x ∈ Z} h̲_{m^A}(T, x) ≥ h̲(Z, T)`, and the same for the
upper quantities and the packing entropy. The equality is Proposition 6.12; the inequality is
Corollary 6.14 applied to the normalized `m^A`. Blueprint node `meas:remarks`. -/
theorem iSup_orbitComplexities_eq_iSup_localEntropy_universalMeasure (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (hP : ComputablePresentationIn P A)
    (hTA : IsRepresentedMapIn P P A T) (Z : Set X) :
    (⨆ x ∈ Z, (orbitComplexities P T A x).1) =
        ⨆ x ∈ Z, (localEntropy (universalMeasure P A) T x).1 ∧
      (⨆ x ∈ Z, (orbitComplexities P T A x).2) =
        ⨆ x ∈ Z, (localEntropy (universalMeasure P A) T x).2 ∧
      lowerEntropy T Z ≤ ⨆ x ∈ Z, (localEntropy (universalMeasure P A) T x).1 ∧
      upperEntropy P T Z ≤ ⨆ x ∈ Z, (localEntropy (universalMeasure P A) T x).2 := by
  have heq := orbitComplexities_eq_localEntropy_universalMeasure P T hT A hP hTA
  have := (localEntropy_normalized P T A (P.ι 0)).1
  refine ⟨by simp only [heq], by simp only [heq], ?_, ?_⟩
  · rw [lowerEntropy_eq_iInf_measure P T hT Z]
    refine iInf₂_le_of_le ((universalMeasure P A univ)⁻¹ • universalMeasure P A) this
      (iSup₂_mono fun x _ ↦ ?_)
    rw [(localEntropy_normalized P T A x).2]
  · rw [upperEntropy_eq_iInf_measure P T hT Z]
    refine iInf₂_le_of_le ((universalMeasure P A univ)⁻¹ • universalMeasure P A) this
      (iSup₂_mono fun x _ ↦ ?_)
    rw [(localEntropy_normalized P T A x).2]

/-- Remark 6.15, the equivalence: Corollary 6.14 (`lowerEntropy_eq_iInf_measure`) gives
Theorem 2.1 restricted to admissible oracles, `h̲(Z, T) = min_A sup_{x ∈ Z} K̲^A(x, T)` over the
oracles that compute the metric table and represent `T`. The proof uses only Corollary 6.14 and
the two halves of the remark, not Theorem 2.1. Blueprint node `meas:remarks`. -/
theorem lowerEntropy_eq_iInf_admissible (P : Presentation X) (T : X → X) (hT : Continuous T)
    (Z : Set X) :
    lowerEntropy T Z = ⨅ (A : Set ℕ) (_ : ComputablePresentationIn P A ∧
      IsRepresentedMapIn P P A T), ⨆ x ∈ Z, (orbitComplexities P T A x).1 := by
  refine le_antisymm (le_iInf₂ fun A hA ↦ ?_) ?_
  · obtain ⟨h1, -, h3, -⟩ :=
      iSup_orbitComplexities_eq_iSup_localEntropy_universalMeasure P T hT A hA.1 hA.2 Z
    rw [h1]
    exact h3
  · rw [lowerEntropy_eq_iInf_measure P T hT Z]
    refine le_iInf₂ fun μ hμ ↦ ?_
    obtain ⟨C, hC⟩ := exists_cone_iSup_orbitComplexities_le P T hT μ
    obtain ⟨hA, hZ⟩ := hC C (TuringReducible.refl _)
    exact iInf₂_le_of_le C ⟨hA.1, hA.2.1⟩ (hZ Z).1

/-- Remark 6.15, the equivalence for the upper quantities: Corollary 6.14
(`upperEntropy_eq_iInf_measure`) gives `h̄(Z, T) = min_A sup_{x ∈ Z} K̄^A(x, T)` over the oracles
that compute the metric table and represent `T`. Blueprint node `meas:remarks`. -/
theorem upperEntropy_eq_iInf_admissible (P : Presentation X) (T : X → X) (hT : Continuous T)
    (Z : Set X) :
    upperEntropy P T Z = ⨅ (A : Set ℕ) (_ : ComputablePresentationIn P A ∧
      IsRepresentedMapIn P P A T), ⨆ x ∈ Z, (orbitComplexities P T A x).2 := by
  refine le_antisymm (le_iInf₂ fun A hA ↦ ?_) ?_
  · obtain ⟨-, h2, -, h4⟩ :=
      iSup_orbitComplexities_eq_iSup_localEntropy_universalMeasure P T hT A hA.1 hA.2 Z
    rw [h2]
    exact h4
  · rw [upperEntropy_eq_iInf_measure P T hT Z]
    refine le_iInf₂ fun μ hμ ↦ ?_
    obtain ⟨C, hC⟩ := exists_cone_iSup_orbitComplexities_le P T hT μ
    obtain ⟨hA, hZ⟩ := hC C (TuringReducible.refl _)
    exact iInf₂_le_of_le C ⟨hA.1, hA.2.1⟩ (hZ Z).2

/-! ### Remark 7.2 -/

/-- Remark 7.2 (algorithmic form of Lemma 7.1): if `A` is admissible for two Borel probability
measures `μ` and `ν`, then at every point of `R_A^ν`, `Φ_ν = Ψ^A ≤ Φ_μ` coordinatewise: a
measure has, at its own random points, the smallest local entropies among the measures
computable from the same oracle. Blueprint node `meas:remarks`. -/
theorem orbitComplexities_eq_localEntropy_le_of_mem_randomPoints (P : Presentation X)
    (T : X → X) (hT : Continuous T) (A : Set ℕ) (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsMeasureAdmissible P T μ A)
    (hν : IsMeasureAdmissible P T ν A) {x : X} (hx : x ∈ randomPoints P A ν) :
    orbitComplexities P T A x = localEntropy ν T x ∧
      (localEntropy ν T x).1 ≤ (localEntropy μ T x).1 ∧
      (localEntropy ν T x).2 ≤ (localEntropy μ T x).2 := by
  have heq := orbitComplexities_eq_localEntropy P T hT A ν hν hx
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact orbitComplexities_le_localEntropy P T hT A μ prob_le_one hμ x

/-! ### Remark 7.9 -/

section kernel

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace X] [BorelSpace X] in
/-- A space with a presentation is separable, hence second countable. -/
private lemma secondCountable_of_presentation (P : Presentation X) : SecondCountableTopology X := by
  have : TopologicalSpace.SeparableSpace X :=
    P.dense.separableSpace continuous_of_discreteTopology
  exact UniformSpace.secondCountable_of_separable X

omit [MetricSpace X] [BorelSpace X] in
/-- The mixture of a Markov kernel against a probability measure is a probability measure. -/
private lemma isProbabilityMeasure_bind (Q : Measure Ω) [IsProbabilityMeasure Q]
    (κ : Kernel Ω X) [IsMarkovKernel κ] : IsProbabilityMeasure (Q.bind κ) := by
  rw [← Measure.snd_compProd Q κ]
  infer_instance

/-- Remark 7.9, first claim: in the setting of §7.1 (`μ = ∫ κ ω dQ(ω)`, `M = Q ⊗ κ`), for an
oracle `A` admissible for `μ`, for `M`-almost every `(ω, x)` the point `x` is `μ`-random
relative to `A` and `Φ_μ(x) = Ψ^A(x)` (the second marginal of `M` is `μ`).
Blueprint node `meas:remarks`. -/
theorem ae_compProd_orbitComplexities_eq_bind (P : Presentation X) {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (A : Set ℕ) (hA : IsMeasureAdmissible P T (Q.bind κ) A) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), p.2 ∈ randomPoints P A (Q.bind κ) ∧
      orbitComplexities P T A p.2 = localEntropy (Q.bind κ) T p.2 := by
  have := isProbabilityMeasure_bind Q κ
  have h := (ae_mem_randomPoints P A (Q.bind κ)).and
    (ae_orbitComplexities_eq_localEntropy P T hT A (Q.bind κ) hA)
  have hmap : Measure.map Prod.snd (Q ⊗ₘ κ) = Q.bind κ := Measure.snd_compProd Q κ
  have h' : ∀ᵐ y ∂(Measure.map Prod.snd (Q ⊗ₘ κ)), y ∈ randomPoints P A (Q.bind κ) ∧
      orbitComplexities P T A y = localEntropy (Q.bind κ) T y := by
    rw [hmap]
    exact h
  exact ae_of_ae_map measurable_snd.aemeasurable h'

/-- Remark 7.9, second claim, fibrewise: if `A_ω` is admissible for `μ_ω = κ ω`, then for
`κ ω`-almost every `x` the point `x` is `μ_ω`-random relative to `A_ω` and
`Φ_{μ_ω}(x) = Ψ^{A_ω}(x)`, for each `ω`.

The note states this for `M`-almost every `(ω, x)`; for an arbitrary choice `ω ↦ A_ω` the set
of such pairs need not be measurable, so the joint statement is given separately under a
measurability hypothesis (`ae_compProd_orbitComplexities_eq_kernel`).
Blueprint node `meas:remarks`. -/
theorem ae_orbitComplexities_eq_kernel (P : Presentation X) {T : X → X} (hT : Continuous T)
    (κ : Kernel Ω X) [IsMarkovKernel κ] (Aω : Ω → Set ℕ)
    (hAω : ∀ ω, IsMeasureAdmissible P T (κ ω) (Aω ω)) (ω : Ω) :
    ∀ᵐ x ∂(κ ω), x ∈ randomPoints P (Aω ω) (κ ω) ∧
      orbitComplexities P T (Aω ω) x = localEntropy (κ ω) T x :=
  (ae_mem_randomPoints P (Aω ω) (κ ω)).and
    (ae_orbitComplexities_eq_localEntropy P T hT (Aω ω) (κ ω) (hAω ω))

/-- Remark 7.9, second claim, jointly: if `A_ω` is admissible for `κ ω` for every `ω` and the
map `(ω, x) ↦ Ψ^{A_ω}(x)` is measurable, then `Φ_{μ_ω}(x) = Ψ^{A_ω}(x)` for `M`-almost every
`(ω, x)`. The measurability hypothesis is added (see `ae_orbitComplexities_eq_kernel`); it holds
for countable `Ω` (`measurable_orbitComplexities_of_countable`) and for a single oracle
(`measurable_orbitComplexities_const`). Blueprint node `meas:remarks`. -/
theorem ae_compProd_orbitComplexities_eq_kernel (P : Presentation X) {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (Aω : Ω → Set ℕ) (hAω : ∀ ω, IsMeasureAdmissible P T (κ ω) (Aω ω))
    (hmeas : Measurable fun p : Ω × X ↦ orbitComplexities P T (Aω p.1) p.2) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), orbitComplexities P T (Aω p.1) p.2 = localEntropy (κ p.1) T p.2 :=
  have := secondCountable_of_presentation P
  Measure.ae_compProd_of_ae_ae (measurableSet_eq_fun hmeas (measurable_localEntropy_kernel hT κ))
    (Eventually.of_forall fun ω ↦
      ae_orbitComplexities_eq_localEntropy P T hT (Aω ω) (κ ω) (hAω ω))

/-- For a countable label space, `(ω, x) ↦ Ψ^{A_ω}(x)` is measurable for every choice of
oracles. Blueprint node `meas:remarks`. -/
theorem measurable_orbitComplexities_of_countable [Countable Ω] [MeasurableSingletonClass Ω]
    (P : Presentation X) {T : X → X} (hT : Continuous T) (Aω : Ω → Set ℕ) :
    Measurable fun p : Ω × X ↦ orbitComplexities P T (Aω p.1) p.2 :=
  measurable_from_prod_countable_right fun ω ↦ measurable_orbitComplexities P hT (Aω ω)

/-- For a single oracle `B`, `(ω, x) ↦ Ψ^B(x)` is measurable. Blueprint node `meas:remarks`. -/
theorem measurable_orbitComplexities_const (P : Presentation X) {T : X → X}
    (hT : Continuous T) (B : Set ℕ) :
    Measurable fun p : Ω × X ↦ orbitComplexities P T ((fun _ : Ω ↦ B) p.1) p.2 :=
  (measurable_orbitComplexities P hT B).comp measurable_snd

/-- Remark 7.9, Theorem 7.3(a) read as an oracle gain: with `A` admissible for `μ`, oracles
`A_ω ≥_T A` admissible for `κ ω`, and `(ω, x) ↦ Ψ^{A_ω}(x)` measurable, for `M`-almost every
`(ω, x)`: `Φ_{μ_ω}(x) = Ψ^{A_ω}(x)`, `Φ_μ(x) = Ψ^A(x)`, and `Ψ^{A_ω}(x) ≤ Ψ^A(x)`
coordinatewise (`orbitComplexities_mono_oracle`). Blueprint node `meas:remarks`. -/
theorem ae_compProd_orbitComplexities_kernel_le (P : Presentation X) {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (A : Set ℕ) (hA : IsMeasureAdmissible P T (Q.bind κ) A)
    (Aω : Ω → Set ℕ) (hAAω : ∀ ω, charOracle A ≤ᵀ charOracle (Aω ω))
    (hAω : ∀ ω, IsMeasureAdmissible P T (κ ω) (Aω ω))
    (hmeas : Measurable fun p : Ω × X ↦ orbitComplexities P T (Aω p.1) p.2) :
    ∀ᵐ p ∂(Q ⊗ₘ κ), localEntropy (κ p.1) T p.2 = orbitComplexities P T (Aω p.1) p.2 ∧
      localEntropy (Q.bind κ) T p.2 = orbitComplexities P T A p.2 ∧
      (orbitComplexities P T (Aω p.1) p.2).1 ≤ (orbitComplexities P T A p.2).1 ∧
      (orbitComplexities P T (Aω p.1) p.2).2 ≤ (orbitComplexities P T A p.2).2 := by
  filter_upwards [ae_compProd_orbitComplexities_eq_kernel P hT Q κ Aω hAω hmeas,
    ae_compProd_orbitComplexities_eq_bind P hT Q κ A hA] with p h1 h2
  exact ⟨h1.symm, h2.2.symm, orbitComplexities_mono_oracle P T (hAAω p.1) p.2⟩

/-- Remark 7.9, integral affinity as the absence of an oracle gain: under the hypotheses of
`ae_compProd_orbitComplexities_kernel_le` (without the comparison of oracles), integral
affinity `Λ_μ = ∫ Λ_{μ_ω} dQ(ω)` holds if and only if `Ψ^{A_ω}(x) = Ψ^A(x)` for `M`-almost
every `(ω, x)` (Theorem 7.3(b), `kernelEntropyLaw_eq_iff`). Blueprint node `meas:remarks`. -/
theorem kernelEntropyLaw_eq_iff_orbitComplexities (P : Presentation X) {T : X → X}
    (hT : Continuous T) (Q : Measure Ω) [IsProbabilityMeasure Q] (κ : Kernel Ω X)
    [IsMarkovKernel κ] (A : Set ℕ) (hA : IsMeasureAdmissible P T (Q.bind κ) A)
    (Aω : Ω → Set ℕ) (hAω : ∀ ω, IsMeasureAdmissible P T (κ ω) (Aω ω))
    (hmeas : Measurable fun p : Ω × X ↦ orbitComplexities P T (Aω p.1) p.2) :
    Measure.map (fun p : Ω × X ↦ localEntropy (κ p.1) T p.2) (Q ⊗ₘ κ) =
        entropyLaw (Q.bind κ) T ↔
      ∀ᵐ p ∂(Q ⊗ₘ κ), orbitComplexities P T (Aω p.1) p.2 = orbitComplexities P T A p.2 := by
  have := secondCountable_of_presentation P
  rw [kernelEntropyLaw_eq_iff hT Q κ]
  have h1 := ae_compProd_orbitComplexities_eq_kernel P hT Q κ Aω hAω hmeas
  have h2 := ae_compProd_orbitComplexities_eq_bind P hT Q κ A hA
  constructor
  · intro h
    filter_upwards [h, h1, h2] with p hp hp1 hp2
    rw [hp1, hp, hp2.2]
  · intro h
    filter_upwards [h, h1, h2] with p hp hp1 hp2
    rw [← hp1, hp, hp2.2]

end kernel

end Kolmogorov.PointToSet
