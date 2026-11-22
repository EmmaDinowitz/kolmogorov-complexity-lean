/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftKSEntropy
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ExampleFiveFiveUpper
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ExampleFiveFiveLower
import KolmogorovMathlib.AlgorithmicRandomness.OracleSemidecision
import KolmogorovMathlib.PointToSet.Measure.ShiftBaire

/-!
# Supplements to the note: sentences of §4.3, Examples 5.2, 5.4 and 5.5

Formal statements of sentences of E. Dinowitz, *Entropy of non-invariant measures and orbit
complexity of random points*, that the chapter did not state (audit, section 3, "Not stated and
missing"). The items that need `ShiftBernoulli.lean` (§4.4, Example 5.2's numbers, Example 6.8)
are in `NoteSupplementsLate.lean`; the rates in probability of product mixtures are in
`NoteSupplementsAux.lean`.

## §4.3 (information of Bowen balls)

* `noteSupp_lintegral_infoBits_cell`: for a finite measurable partition `ξ`,
  `∫ -log₂ μ(ξ(x)) dμ(x) = H_μ(ξ)`.
* `noteSupp_bowenInformation_le_refinementEntropy`: "`I_n(μ, ε) ≤ H_μ(ξ^n)` for every finite
  Borel partition `ξ` of diameter less than `ε`" (`T` measurable).
* `noteSupp_bowenInformation_shiftMap_eq`, `..._eq_blockEntropy`, `..._eq_lintegral`: on a shift
  with `d_β` and the time-zero partition, `I_n(μ, β^k) = H_μ(ξ^{n+k})` exactly (`n ≥ 1`).

## Random points of mixtures and on cones of oracles

* `noteSupp_randomPoints_add_subset`: a point random for `a μ₁ + b μ₂` (`a + b ≤ 1`) is random
  for `μ₁` or for `μ₂`.
* `noteSupp_exists_cone_orbitComplexities_eq`: if `Φ_μ = c` a.e., then on an upper cone of
  oracles every random point has orbit complexities `c`;
  `noteSupp_orbitComplexities_fst_le_of_ae`: Theorem 4.3(a) at one random point.

## Example 5.4 ("every `μ`-random point has orbit complexity `0`")

* `noteSupp_baire_of_mem_randomPoints` (a Solovay-type test, `∑ p_i < ∞` computably): for a
  presentation with `A`-computable symbols, every random point is eventually `0` and lies in the
  support; `noteSupp_orbitComplexities_baireMeasure_of_mem_randomPoints`: it has
  `Φ_μ(x) = (0, 0)` and `K̲^A = K̄^A = 0` (Theorem 3.3).
* Without the symbol hypothesis: `noteSupp_orbitComplexities_baireMeasure_fst` (`K̲^A = 0` for
  every admissible `A`) and `noteSupp_exists_cone_orbitComplexities_baireMeasure` (both `0` on a
  cone of oracles).

## Example 5.5 ("`z`, `z'` are computable from `0′`, hence not random relative to it")

* `noteSupp_computableInJump_of_limit`: the limit lemma (limit-computable ⇒ `0′`-computable).
* `noteSupp_not_mem_randomPoints_of_computableIn`: an `A`-computable non-atom of a measure with
  `A`-computable cylinders is not random relative to `A`.
* `noteSupp_exampleFiveFive_upper_not_random_of_jump`,
  `noteSupp_exampleFiveFive_lower_not_random_of_jump`: the witnesses of `ExampleFiveFiveUpper`
  and `ExampleFiveFiveLower` (standard presentation `cantorPresentation`) are `0′`-computable
  non-atoms that are `∅`-random but not random relative to any oracle computing `0′`
  (`haltingOracle ≤ᵀ charOracle A`; e.g. the halting set itself,
  `noteSupp_haltingOracle_le_halting`).

Blueprint nodes `meas:information-rate`, `meas:shift`, `meas:random`, `meas:essential`,
`meas:examples`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### §4.3: information of Bowen balls and Shannon entropies of partitions -/

section partition

variable {X : Type*} [MeasurableSpace X]

/-- The contribution `q · (-log₂ q)` of a cell of mass `q ≤ 1` to the mean information is the
entropy term `-q log₂ q`. -/
lemma noteSupp_infoBits_mul_self {q : ℝ≥0∞} (hq : q ≤ 1) :
    infoBits q * q = ENNReal.ofReal (Ergodic.entropyTerm q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [Ergodic.entropyTerm]
  have hqt : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  have hlog : 0 ≤ -Real.logb 2 q.toReal :=
    neg_nonneg.2 (Real.logb_nonpos one_lt_two ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hq)))
  have hq' : q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqt).symm
  rw [infoBits_of_ne hq0]
  nth_rw 2 [hq']
  rw [← ENNReal.ofReal_mul hlog, Ergodic.entropyTerm]
  congr 1
  ring

/-- The mean information of the cells of a finite measurable partition is its Shannon entropy:
if `c x` is the index of the cell containing `x`, then `∫ -log₂ μ(ξ_{c x}) dμ(x) = H_μ(ξ)`.
Blueprint node `meas:information-rate`. -/
theorem noteSupp_lintegral_infoBits_cell (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] {ξ : ι → Set X} (hξ : Ergodic.IsMeasurablePartition ξ) (c : X → ι)
    (hc : ∀ x, x ∈ ξ (c x)) :
    ∫⁻ x, infoBits (μ (ξ (c x))) ∂μ = ENNReal.ofReal (Ergodic.partitionEntropy μ ξ) := by
  classical
  have hpt : ∀ x, infoBits (μ (ξ (c x))) =
      ∑ i, (ξ i).indicator (fun _ ↦ infoBits (μ (ξ i))) x := by
    intro x
    rw [Finset.sum_eq_single (c x)]
    · rw [indicator_of_mem (hc x)]
    · intro i _ hi
      exact indicator_of_notMem (fun hx ↦
        Set.disjoint_left.1 (hξ.disjoint hi) hx (hc x)) _
    · simp
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun i _ ↦ (measurable_const.indicator (hξ.measurableSet i))]
  simp_rw [lintegral_indicator_const (hξ.measurableSet _)]
  rw [Ergodic.partitionEntropy, ENNReal.ofReal_sum_of_nonneg fun i _ ↦
    Ergodic.entropyTerm_nonneg prob_le_one]
  exact Finset.sum_congr rfl fun i _ ↦ noteSupp_infoBits_mul_self prob_le_one

end partition

section general

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- §4.3, "In general `I_n(μ, ε) ≤ H_μ(ξ^n)` for every finite Borel partition `ξ` of diameter
less than `ε`": for a finite measurable partition whose cells have all their distances `< ε`
(implied by diameter `< ε`) and a measurable `T`,
`I_n(μ, ε) = ∫ -log₂ μ(B_n(x, T, ε)) dμ ≤ H_μ(ξ^n)` with `ξ^n = ⋁_{k<n} T^{-k} ξ`.
The cell of `ξ^n` containing `x` lies in `B_n(x, T, ε)`. Blueprint node
`meas:information-rate`. -/
theorem noteSupp_bowenInformation_le_refinementEntropy {T : X → X} (hT : Measurable T)
    (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ξ : ι → Set X} (hξ : Ergodic.IsMeasurablePartition ξ) {ε : ℝ}
    (hdiam : ∀ i, ∀ x ∈ ξ i, ∀ y ∈ ξ i, dist x y < ε) (n : ℕ) :
    bowenInformation μ T n ε ≤ ENNReal.ofReal (Ergodic.refinementEntropy μ T ξ n) := by
  have hcov : ∀ x, ∃ i, x ∈ ξ i := fun x ↦ Set.mem_iUnion.1 (hξ.iUnion_eq ▸ Set.mem_univ x)
  choose idx hidx using hcov
  set c : X → Fin n → ι := fun x k ↦ idx (T^[k] x) with hc
  have hmem : ∀ x, x ∈ Ergodic.refinement T ξ n (c x) := fun x ↦
    Set.mem_iInter.2 fun k ↦ hidx (T^[k] x)
  rw [Ergodic.refinementEntropy, ← noteSupp_lintegral_infoBits_cell μ (hξ.refinement hT n) c hmem,
    bowenInformation]
  refine lintegral_mono fun x ↦ infoBits_antitone (measure_mono fun y hy ↦ ?_)
  refine mem_bowenBall_iff.2 fun k hk ↦ ?_
  exact hdiam _ _ (hidx (T^[k] x)) _ (Set.mem_iInter.1 hy ⟨k, hk⟩)

end general

section shift

variable {α : Type*} [MetricSpace (ℕ → α)] [MeasurableSpace (ℕ → α)] {β : ℝ}

/-- For a first-difference metric the cylinders `[x↾m]` are open, hence measurable. -/
lemma noteSupp_measurableSet_cylinder [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (x : ℕ → α) (m : ℕ) :
    MeasurableSet (PiNat.cylinder x m) := by
  rcases m with _ | j
  · simp
  have h := bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd x le_rfl j
  rw [add_comm] at h
  rw [← h]
  have hball : bowenBall (shiftMap : (ℕ → α) → ℕ → α) 1 x (β ^ j) = Metric.ball x (β ^ j) := by
    ext y
    simp [mem_bowenBall_iff, dist_comm]
  rw [hball]
  exact measurableSet_ball

/-- For a first-difference metric the cylinders of a fixed length form a finite measurable
partition: the refinement `ξ^m` of the partition `ξ` by the first symbol. -/
lemma noteSupp_isMeasurablePartition_refinement [BorelSpace (ℕ → α)] (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (m : ℕ) :
    Ergodic.IsMeasurablePartition
      (Ergodic.refinement shiftMap (shiftKS_symbolPartition (α := α)) m) := by
  have hmeas : Measurable (shiftMap : (ℕ → α) → ℕ → α) :=
    (continuous_shiftMap hβ hβ₁ hd).measurable
  refine Ergodic.IsMeasurablePartition.refinement hmeas ⟨fun a ↦ ?_, ?_, ?_⟩ m
  · have : shiftKS_symbolPartition a = PiNat.cylinder (fun _ ↦ a) 1 := by
      ext z
      simp [shiftKS_symbolPartition, PiNat.mem_cylinder_iff]
    rw [this]
    exact noteSupp_measurableSet_cylinder hβ hβ₁ hd _ 1
  · intro a b hab
    exact Set.disjoint_left.2 fun z ha hb ↦ hab (ha.symm.trans hb)
  · exact Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 ⟨z 0, rfl⟩

/-- §4.3, "on a shift with `d_β` and the time-zero partition `ξ`, `I_n(μ, β^k) = H_μ(ξ^{n+k})`
exactly": for `n ≥ 1` and a probability measure, the Bowen information at the scale `β^k` is
the Shannon entropy of the refinement `ξ^{n+k} = ⋁_{j<n+k} σ^{-j} ξ` of the partition `ξ` by
the first symbol (a finite-`n` identity). Blueprint node `meas:shift`. -/
theorem noteSupp_bowenInformation_shiftMap_eq [Fintype α] [DecidableEq α] [BorelSpace (ℕ → α)]
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α))
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    bowenInformation μ shiftMap n (β ^ k) =
      ENNReal.ofReal (Ergodic.refinementEntropy μ shiftMap shiftKS_symbolPartition (n + k)) := by
  have hcyl : ∀ x : ℕ → α, PiNat.cylinder x (n + k) =
      Ergodic.refinement shiftMap shiftKS_symbolPartition (n + k) (fun i ↦ x i) := by
    intro x
    rw [shiftKS_refinement_eq_wordCylinder]
    ext y
    simp [wordCylinder, PiNat.mem_cylinder_iff, Fin.forall_iff]
  rw [Ergodic.refinementEntropy, ← noteSupp_lintegral_infoBits_cell μ
    (noteSupp_isMeasurablePartition_refinement hβ hβ₁ hd (n + k)) (fun x i ↦ x i)
    (fun x ↦ hcyl x ▸ PiNat.self_mem_cylinder x _), bowenInformation]
  simp only [bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd _ hn k, hcyl]

/-- §4.3, the same identity with the block entropy of `ShiftGeneric`:
`I_n(μ, β^k) = H_μ(ξ^{n+k}) = -∑_{|w| = n+k} μ[w] log₂ μ[w]` for `n ≥ 1`.
Blueprint node `meas:shift`. -/
theorem noteSupp_bowenInformation_shiftMap_eq_blockEntropy [Fintype α] [BorelSpace (ℕ → α)]
    (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α))
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    bowenInformation μ shiftMap n (β ^ k) = ENNReal.ofReal (blockEntropy μ (n + k)) := by
  classical
  rw [noteSupp_bowenInformation_shiftMap_eq hβ hβ₁ hd μ hn k,
    shiftKS_blockEntropy_eq_refinementEntropy]

/-- §4.3 on a shift: `I_n(μ, β^k) = ∫ -log₂ μ[x↾(n+k)] dμ(x)` for `n ≥ 1` (any measure).
Blueprint node `meas:shift`. -/
theorem noteSupp_bowenInformation_shiftMap_eq_lintegral (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y) (μ : Measure (ℕ → α))
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    bowenInformation μ shiftMap n (β ^ k) =
      ∫⁻ x, infoBits (μ (PiNat.cylinder x (n + k))) ∂μ := by
  simp only [bowenInformation, bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd _ hn k]

end shift

/-! ### Random points of mixtures, and random points on a cone of oracles -/

section general

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A point random for a mixture `a μ₁ + b μ₂` (`a + b ≤ 1`) is random for `μ₁` or for `μ₂`: if
`x` lies in all levels of a `μ₁`-test `U` and of a `μ₂`-test `V`, it lies in all levels of the
`μ`-test `U_m ∩ V_m`, of measure `≤ a 2^{-m} + b 2^{-m} ≤ 2^{-m}` (Example 5.2: "every
`μ`-random point is `μ₁`-random or `μ₂`-random"). No computability of the weights or of the
measures is needed. Blueprint node `meas:random`. -/
theorem noteSupp_randomPoints_add_subset (P : Presentation X) (A : Set ℕ)
    (hP : ComputablePresentationIn P A) (μ₁ μ₂ : Measure X) {a b : ℝ≥0∞} (hab : a + b ≤ 1) :
    randomPoints P A (a • μ₁ + b • μ₂) ⊆ randomPoints P A μ₁ ∪ randomPoints P A μ₂ := by
  intro x hx
  by_contra hn
  simp only [mem_union, randomPoints, mem_ofPred_eq, not_or, not_forall, not_exists,
    not_not] at hn
  obtain ⟨⟨U, hU, hxU⟩, ⟨V, hV, hxV⟩⟩ := hn
  have hμ : ∀ m, (a • μ₁ + b • μ₂) (U m ∩ V m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := fun m ↦
    calc (a • μ₁ + b • μ₂) (U m ∩ V m) = a * μ₁ (U m ∩ V m) + b * μ₂ (U m ∩ V m) := by
          simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      _ ≤ a * (2 : ℝ≥0∞)⁻¹ ^ m + b * (2 : ℝ≥0∞)⁻¹ ^ m := by
          gcongr
          · exact (measure_mono inter_subset_left).trans (hU.2 m)
          · exact (measure_mono inter_subset_right).trans (hV.2 m)
      _ = (a + b) * (2 : ℝ≥0∞)⁻¹ ^ m := (add_mul _ _ _).symm
      _ ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ m := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ m := one_mul _
  obtain ⟨m, hm⟩ := hx (fun m ↦ U m ∩ V m) ⟨IsCeOpenFamilyIn.inter P A hP hU.1 hV.1, hμ⟩
  exact hm ⟨hxU m, hxV m⟩

variable [BorelSpace X]

/-- If the local entropies of `μ` equal `c` almost everywhere, then on an upper cone of oracles
(all admissible) every `μ`-random point has orbit complexities `c`: the exceptional null set is
avoided by the random points relative to a strong enough oracle
(`exists_oracle_randomPoints_disjoint`), and at random points the orbit complexities are the
local entropies (Theorem 3.3, `orbitComplexities_eq_localEntropy`).
Blueprint node `meas:essential`. -/
theorem noteSupp_exists_cone_orbitComplexities_eq (P : Presentation X) (T : X → X)
    (hT : Continuous T) (μ : Measure X) [IsProbabilityMeasure μ] {c : ℝ≥0∞ × ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, localEntropy μ T x = c) :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      IsMeasureAdmissible P T μ B ∧
        ∀ x ∈ randomPoints P B μ, orbitComplexities P T B x = c := by
  obtain ⟨C₁, hC₁⟩ := exists_oracle_randomPoints_disjoint P μ (ae_iff.1 h)
  obtain ⟨C₂, hC₂⟩ := exists_measureAdmissible_base P T hT μ
  refine ⟨oracleJoin C₁ C₂, fun B hB ↦ ?_⟩
  have hBa := hC₂ B ((oracle_joins_right C₁ C₂).trans hB)
  refine ⟨hBa, fun x hx ↦ ?_⟩
  rw [orbitComplexities_eq_localEntropy P T hT B μ hBa hx]
  by_contra hne
  exact Set.disjoint_left.1 (hC₁ B ((oracle_joins C₁ C₂).trans hB)) hx hne

/-- Theorem 4.3(a) at a single random point: if `h̲_μ ≤ s` almost everywhere, then for every
admissible oracle the lower orbit complexity is at most `s` at every `μ`-random point.
Blueprint node `meas:essential`. -/
theorem noteSupp_orbitComplexities_fst_le_of_ae (P : Presentation X) (T : X → X)
    (hT : Continuous T) (A : Set ℕ) (μ : Measure X) [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) {s : ℝ≥0∞} (h : ∀ᵐ x ∂μ, (localEntropy μ T x).1 ≤ s)
    {x : X} (hx : x ∈ randomPoints P A μ) : (orbitComplexities P T A x).1 ≤ s := by
  refine le_trans ?_ (essSup_le_of_ae_le s h)
  rw [← iSup_randomPoints_orbitComplexities_fst P T hT A μ hA]
  exact le_iSup₂ (f := fun y _ ↦ (orbitComplexities P T A y).1) x hx

end general

section cantor

attribute [local instance] cantorMetricSpace

/-- The cylinders of a point shrink to the point. -/
lemma noteSupp_iInter_cylinder {α : Type*} (z : ℕ → α) : ⋂ n, PiNat.cylinder z n = {z} := by
  ext y
  simp only [mem_iInter, PiNat.mem_cylinder_iff, mem_singleton_iff]
  exact ⟨fun h ↦ funext fun i ↦ h (i + 1) i (Nat.lt_succ_self i), fun h n i _ ↦ by rw [h]⟩

/-- An `A`-computable point that is not an atom is not random relative to `A`: if the cylinder
masses of `μ` are `A`-computable, `z` is `A`-computable and `μ{z} = 0`, the prefixes of `z` of
mass `< 2^{-m}` form a test (relative to `A`) that `z` fails. Blueprint node `meas:examples`. -/
theorem noteSupp_not_mem_randomPoints_of_computableIn {A : Set ℕ} (μ : Measure (ℕ → Bool))
    [IsFiniteMeasure μ] (hμ : IsComputableWordMeasureIn A μ) {z : ℕ → Bool}
    (hz : ComputableIn {charOracle A} z) (h0 : μ {z} = 0) :
    z ∉ randomPoints cantorPresentation A μ := by
  rw [cantorPres_randomPoints_eq]
  intro hrand
  set E : ℕ × List Bool → Prop := fun mu ↦
    (∀ k (h : k < mu.2.length), z k = mu.2.get ⟨k, h⟩) ∧
      (μ (listCylinder mu.2)).toReal < (((2 : ℚ)⁻¹ ^ mu.1 : ℚ) : ℝ) with hE
  have hRE : IsREIn A E := by
    refine IsREIn.and ?_ ?_
    · refine IsREIn.list_forall_get (F := fun d : ℕ × ℕ × Bool ↦ z d.2.1 = d.2.2) ?_
      refine isREIn_of_computableIn_decide A _ ?_
      exact primrec_decideEq.to_comp.computableIn.comp
        ((hz.comp (Computable.fst.comp Computable.snd).computableIn).pair
          (Computable.snd.comp Computable.snd).computableIn)
    · have h := birkhoff_computableIn_lt A _ hμ
      exact h.comp ((Computable.snd.pair
        (computable_inv_two_pow.comp Computable.fst)).computableIn)
  -- the cylinder of an element of `E` is a cylinder of `z`
  have hcyl : ∀ m u, E (m, u) → listCylinder u = PiNat.cylinder z u.length := by
    intro m u hu
    ext y
    simp only [listCylinder, mem_ofPred_eq, PiNat.mem_cylinder_iff]
    constructor
    · intro h i hi
      rw [h i hi, hu.1 i hi]
      rfl
    · intro h i hi
      rw [h i hi, hu.1 i hi]
      rfl
  set V : ℕ → Set (ℕ → Bool) := fun m ↦ ⋃ u ∈ {u | E (m, u)}, listCylinder u with hV
  have hμV : ∀ m, μ (V m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    by_cases hne : ∃ u, E (m, u)
    · classical
      have hex : ∃ n, ∃ u, E (m, u) ∧ u.length = n := ⟨_, hne.choose, hne.choose_spec, rfl⟩
      obtain ⟨u₀, hu₀, hlen⟩ := Nat.find_spec hex
      have hsub : V m ⊆ listCylinder u₀ := by
        refine iUnion₂_subset fun u hu ↦ ?_
        rw [hcyl m u hu, hcyl m u₀ hu₀, hlen]
        exact PiNat.cylinder_anti z (Nat.find_min' hex ⟨u, hu, rfl⟩)
      refine (measure_mono hsub).trans ?_
      have h2 := hu₀.2
      rw [CantorPres.cast_inv_two_pow_real] at h2
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      calc ENNReal.ofReal (μ (listCylinder u₀)).toReal ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) :=
            ENNReal.ofReal_le_ofReal h2.le
        _ = (2 : ℝ≥0∞)⁻¹ ^ m := by
            rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
              ENNReal.ofReal_ofNat]
    · push Not at hne
      have : V m = ∅ := by
        simp only [hV]
        exact Set.eq_empty_of_forall_notMem fun y hy ↦ by
          obtain ⟨u, hu, -⟩ := mem_iUnion₂.1 hy
          exact hne u hu
      rw [this, measure_empty]
      exact zero_le
  obtain ⟨m, hm⟩ := hrand V ⟨E, hRE, fun m ↦ rfl, hμV⟩
  -- but `z ∈ V m`, since `μ[z↾n] → μ{z} = 0`
  have ht : Tendsto (fun n ↦ μ (PiNat.cylinder z n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ (measurableSet_cantor_cylinder z n).nullMeasurableSet)
      (fun _ _ h ↦ PiNat.cylinder_anti z h) ⟨0, measure_ne_top μ _⟩
    rwa [noteSupp_iInter_cylinder, h0] at this
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) := by
    rw [ENNReal.ofReal_pos]; positivity
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hpos)).exists
  refine hm (mem_iUnion₂.2 ⟨wordPrefix z n, ⟨fun k hk ↦ ?_, ?_⟩, ?_⟩)
  · simp [wordPrefix]
  · rw [CantorPres.cast_inv_two_pow_real, cantorPres_listCylinder_wordPrefix]
    exact (ENNReal.toReal_lt_of_lt_ofReal hn)
  · exact mem_listCylinder_wordPrefix z n


end cantor

/-! ### Example 5.4: every random point has orbit complexity `0` -/

section baire

attribute [local instance] baireMetricSpace

/-- The tail of `∑ p_i` with `p_i = (i + 2)^{-2}`: `∑_{j} p_{j+N} ≤ 1/(N + 1)` (telescoping,
`p_i ≤ 1/(i + 1) - 1/(i + 2)`). -/
lemma noteSupp_tsum_baireProb_tail_le (N : ℕ) :
    ∑' j, ENNReal.ofReal (baireProb (j + N)) ≤ ENNReal.ofReal (((N : ℝ) + 1)⁻¹) := by
  refine ENNReal.tsum_le_of_sum_range_le fun K ↦ ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ ↦ (baireProb_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have key : ∀ K : ℕ, ∑ j ∈ Finset.range K, baireProb (j + N) ≤
      ((N : ℝ) + 1)⁻¹ - ((N : ℝ) + K + 1)⁻¹ := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have h : baireProb (K + N) ≤ ((N : ℝ) + K + 1)⁻¹ - ((N : ℝ) + (K + 1 : ℕ) + 1)⁻¹ := by
        unfold baireProb
        push_cast
        have h1 : (0 : ℝ) < N + K + 1 := by positivity
        rw [inv_sub_inv (by positivity) (by positivity), le_div_iff₀ (by positivity)]
        field_simp
        nlinarith
      linarith
  have hpos : (0 : ℝ) ≤ ((N : ℝ) + K + 1)⁻¹ := by positivity
  linarith [key K]

/-- Example 5.4: the `i`-th coordinate is nonzero with probability at most `p_i`. -/
lemma noteSupp_baireMeasure_ne_zero_le (i : ℕ) :
    baireMeasure {x : ℕ → ℕ | x i ≠ 0} ≤ ENNReal.ofReal (baireProb i) := by
  rw [show {x : ℕ → ℕ | x i ≠ 0} = (fun x : ℕ → ℕ ↦ x i) ⁻¹' {k | k ≠ 0} from rfl,
    baireMeasure, baireMeasureOf, infinitePi_preimage_eval_nat]
  exact baireFactorOf_ne_zero_le _ i

/-- Example 5.4: almost every point has `x_i ≤ 2^{L_i}` for all `i`. -/
lemma noteSupp_baireMeasure_out_eq_zero :
    baireMeasure {x : ℕ → ℕ | ∃ i, 2 ^ baireLength i < x i} = 0 := by
  rw [show {x : ℕ → ℕ | ∃ i, 2 ^ baireLength i < x i} =
      ⋃ i, (fun x : ℕ → ℕ ↦ x i) ⁻¹' {k | 2 ^ baireLength i < k} by ext; simp]
  refine measure_iUnion_null fun i ↦ ?_
  rw [baireMeasure, baireMeasureOf, infinitePi_preimage_eval_nat]
  exact baireFactorOf_eq_zero _ i fun k hk ↦ baireWeight_eq_zero _ i hk

/-- The index predicate of the Solovay-type test of Example 5.4: a word `w` of length `i + 1`
is listed at level `m` when `i ≥ 2^m` and `w_i ≠ 0`, or when `w_i > 2^{L_i}` (outside the
support). -/
def noteSupp_baireTestIdx (q : ℕ × ℕ × List ℕ) : Prop :=
  (2 ^ q.1 ≤ q.2.1 ∧ q.2.2.length = q.2.1 + 1 ∧ q.2.2.getD q.2.1 0 ≠ 0) ∨
    (q.2.2.length = q.2.1 + 1 ∧ 2 ^ baireLength q.2.1 < q.2.2.getD q.2.1 0)

/-- The index predicate of the Example 5.4 test is decidable. -/
instance noteSupp_decidablePred_baireTestIdx : DecidablePred noteSupp_baireTestIdx := fun q ↦ by
  unfold noteSupp_baireTestIdx; infer_instance

/-- The index predicate of the Example 5.4 test is computable. -/
lemma noteSupp_computable_baireTestIdx :
    Computable fun q ↦ decide (noteSupp_baireTestIdx q) := by
  have hpow : Primrec₂ fun a b : ℕ ↦ a ^ b := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hi : Primrec fun q : ℕ × ℕ × List ℕ ↦ q.2.1 := Primrec.fst.comp Primrec.snd
  have hw : Primrec fun q : ℕ × ℕ × List ℕ ↦ q.2.2 := Primrec.snd.comp Primrec.snd
  have hlen : Primrec fun q : ℕ × ℕ × List ℕ ↦ q.2.2.length := Primrec.list_length.comp hw
  have hget : Primrec fun q : ℕ × ℕ × List ℕ ↦ q.2.2.getD q.2.1 0 :=
    (Primrec.list_getD 0).comp hw hi
  have h1 : Primrec fun q : ℕ × ℕ × List ℕ ↦ decide (2 ^ q.1 ≤ q.2.1) :=
    (PrimrecRel.comp Primrec.nat_le (hpow.comp (Primrec.const 2) Primrec.fst) hi).decide
  have h2 : Primrec fun q : ℕ × ℕ × List ℕ ↦ decide (q.2.2.length = q.2.1 + 1) :=
    (PrimrecRel.comp Primrec.eq hlen (Primrec.succ.comp hi)).decide
  have h3 : Primrec fun q : ℕ × ℕ × List ℕ ↦ decide (q.2.2.getD q.2.1 0 = 0) :=
    (PrimrecRel.comp Primrec.eq hget (Primrec.const 0)).decide
  have h4 : Primrec fun q : ℕ × ℕ × List ℕ ↦ decide (2 ^ baireLength q.2.1 < q.2.2.getD q.2.1 0) :=
    (PrimrecRel.comp Primrec.nat_lt (hpow.comp (Primrec.const 2)
      (hpow.comp (Primrec.nat_add.comp hi (Primrec.const 2)) (Primrec.const 2))) hget).decide
  refine (Primrec.or.comp (Primrec.and.comp h1 (Primrec.and.comp h2 (Primrec.not.comp h3)))
    (Primrec.and.comp h2 h4)).to_comp.of_eq fun q ↦ ?_
  simp [noteSupp_baireTestIdx, baireLength]

/-- Example 5.4, "since `∑ p_i < ∞` is computable" (a Solovay-type test): for a presentation
of Baire space whose ideal points have `A`-computable symbols and an `A`-computable metric table,
every `μ`-random point relative to `A` has only finitely many nonzero coordinates, and all its
coordinates lie in the support `x_i ≤ 2^{L_i}`. The levels
`W_m = {∃ i ≥ 2^m, x_i ≠ 0} ∪ {∃ i, x_i > 2^{L_i}}` are `A`-c.e. unions of cylinders of measure
`≤ ∑_{i ≥ 2^m} p_i ≤ 2^{-m}`. Blueprint node `meas:examples`. -/
theorem noteSupp_baire_of_mem_randomPoints (P : Presentation (ℕ → ℕ)) (A : Set ℕ)
    (hPc : ComputablePresentationIn P A)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) {x : ℕ → ℕ}
    (hx : x ∈ randomPoints P A baireMeasure) :
    ∃ N, (∀ i, N ≤ i → x i = 0) ∧ ∀ i, x i ≤ 2 ^ baireLength i := by
  have hL : IsCeOpenFamilyIn P A (listCylinder : List ℕ → Set (ℕ → ℕ)) :=
    isCeOpenFamilyIn_listCylinder (β := 1 / 2) (by norm_num) (by norm_num)
      (fun _ _ ↦ baireMetricSpace_dist_eq) P A hPc hP
  set U : ℕ × ℕ × List ℕ → Set (ℕ → ℕ) := fun q ↦
    if noteSupp_baireTestIdx q then listCylinder q.2.2 else ∅ with hU_def
  have hU : IsCeOpenFamilyIn P A U :=
    (hL.comp (Computable.snd.comp Computable.snd)).ite noteSupp_computable_baireTestIdx
  set W : ℕ → Set (ℕ → ℕ) := fun m ↦ ⋃ k, U (m, k) with hW_def
  have hW : IsCeOpenFamilyIn P A W := hU.iUnion
  -- a point of a cylinder `[w]` has `y i = w.getD i 0` for `i < |w|`
  have hcyl : ∀ (w : List ℕ) (y : ℕ → ℕ) (i : ℕ), y ∈ listCylinder w → i < w.length →
      y i = w.getD i 0 := fun w y i hy hi ↦ by
    rw [hy i hi, List.getD_eq_getElem _ _ hi]
  have hsub : ∀ m, W m ⊆ (⋃ j, {y : ℕ → ℕ | y (j + 2 ^ m) ≠ 0}) ∪
      {y : ℕ → ℕ | ∃ i, 2 ^ baireLength i < y i} := by
    intro m y hy
    obtain ⟨⟨i, w⟩, hy⟩ := mem_iUnion.1 hy
    simp only [hU_def] at hy
    split_ifs at hy with hc
    · rcases hc with ⟨h1, h2, h3⟩ | ⟨h2, h4⟩
      · refine Or.inl (mem_iUnion.2 ⟨i - 2 ^ m, ?_⟩)
        simp only [mem_ofPred_eq]
        rw [Nat.sub_add_cancel h1, hcyl w y i hy (by simp only at h2; omega)]
        exact h3
      · refine Or.inr ⟨i, ?_⟩
        rw [hcyl w y i hy (by simp only at h2; omega)]
        exact h4
    · exact absurd hy (notMem_empty y)
  have hμ : ∀ m, baireMeasure (W m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    refine (measure_mono (hsub m)).trans ((measure_union_le _ _).trans ?_)
    rw [noteSupp_baireMeasure_out_eq_zero, add_zero]
    refine (measure_iUnion_le _).trans ?_
    refine (ENNReal.tsum_le_tsum fun j ↦ noteSupp_baireMeasure_ne_zero_le (j + 2 ^ m)).trans ?_
    refine (noteSupp_tsum_baireProb_tail_le (2 ^ m)).trans ?_
    have h2 : ((((2 : ℕ) ^ m : ℕ) : ℝ) + 1)⁻¹ ≤ (2 : ℝ)⁻¹ ^ m := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (by push_cast; linarith)
    refine (ENNReal.ofReal_le_ofReal h2).trans_eq ?_
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  obtain ⟨m, hm⟩ := hx W ⟨hW, hμ⟩
  have hlen : ∀ i, (wordPrefix x (i + 1)).length = i + 1 := fun i ↦ List.length_ofFn
  have hget : ∀ i, (wordPrefix x (i + 1)).getD i 0 = x i := fun i ↦ by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
    simp only [wordPrefix, List.getElem_ofFn]
  have hmemW : ∀ i, noteSupp_baireTestIdx (m, i, wordPrefix x (i + 1)) → x ∈ W m := by
    intro i hi
    refine mem_iUnion.2 ⟨(i, wordPrefix x (i + 1)), ?_⟩
    simp only [hU_def, hi, ↓reduceIte]
    exact mem_listCylinder_wordPrefix x (i + 1)
  refine ⟨2 ^ m, fun i hi ↦ ?_, fun i ↦ ?_⟩
  · by_contra h
    exact hm (hmemW i (Or.inl ⟨hi, hlen i, by rw [hget]; exact h⟩))
  · by_contra h
    exact hm (hmemW i (Or.inr ⟨hlen i, by simp only; rw [hget]; omega⟩))

/-- Example 5.4, pointwise: if `x` is eventually `0` and lies in the support, then
`-log₂ μ[x↾n]` is bounded and `Φ_μ(x) = (0, 0)`. Blueprint node `meas:examples`. -/
theorem noteSupp_localEntropy_baireMeasure_of_eventually {x : ℕ → ℕ} {N : ℕ}
    (hev : ∀ i, N ≤ i → x i = 0) (hsupp : ∀ i, x i ≤ 2 ^ baireLength i) :
    localEntropy baireMeasure shiftMap x = (0, 0) := by
  have hpos : ∀ i, baireFactor i {x i} ≠ 0 := by
    intro i
    rw [baireFactor, baireFactorOf_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    unfold baireWeight
    split_ifs with h0 h1
    · linarith [baireProb_le i]
    · exact div_pos (baireProb_pos i) (by positivity)
    · exact absurd (hsupp i) h1
  set f : ℕ → ℝ≥0∞ := fun i ↦ infoBits (baireFactor i {x i}) with hf
  set g : ℕ → ℝ≥0∞ := fun i ↦ infoBits (ENNReal.ofReal (1 - baireProb i)) with hg
  set s : Finset ℕ := Finset.range N with hs
  set M := ∑ i ∈ s, f i + ∑' i, g i with hM
  have hMt : M ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨ENNReal.sum_ne_top.2 fun i _ ↦ (infoBits_lt_top (hpos i)).ne,
      tsum_infoBits_one_sub_baireProb_ne_top⟩
  have hbd : ∀ n, infoBits (baireMeasure (PiNat.cylinder x n)) ≤ M := by
    intro n
    rw [baireMeasure, baireMeasureOf, infoBits_infinitePi_cylinder_nat]
    have hfg : ∀ i, f i ≤ (s : Set ℕ).indicator f i + g i := fun i ↦ by
      by_cases hi : i ∈ s
      · rw [indicator_of_mem (by simpa using hi)]
        exact le_self_add
      · rw [indicator_of_notMem (by simpa using hi), zero_add]
        have : x i = 0 := hev i (by simpa [hs] using hi)
        simp [hf, hg, this, baireFactor, baireFactorOf_singleton, baireWeight]
    calc ∑ i ∈ Finset.range n, f i
        ≤ ∑ i ∈ Finset.range n, ((s : Set ℕ).indicator f i + g i) :=
          Finset.sum_le_sum fun i _ ↦ hfg i
      _ = ∑ i ∈ Finset.range n, (s : Set ℕ).indicator f i + ∑ i ∈ Finset.range n, g i :=
          Finset.sum_add_distrib
      _ ≤ ∑' i, (s : Set ℕ).indicator f i + ∑' i, g i :=
          add_le_add (ENNReal.sum_le_tsum _) (ENNReal.sum_le_tsum _)
      _ = M := by
          rw [tsum_eq_sum (s := s) fun i hi ↦ indicator_of_notMem (by simpa using hi) _]
          congr 1
          exact Finset.sum_congr rfl fun i hi ↦ indicator_of_mem (by simpa using hi) _
  rw [localEntropy_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ baireMetricSpace_dist_eq)]
  have ht : Tendsto (fun n : ℕ ↦ M / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hMt)
  have hls : limsup (fun n : ℕ ↦ infoBits (baireMeasure (PiNat.cylinder x n)) / n) atTop ≤ 0 :=
    (limsup_le_limsup (.of_forall fun n ↦ ENNReal.div_le_div_right (hbd n) _)).trans
      ht.limsup_eq.le
  exact Prod.ext (le_antisymm (le_trans liminf_le_limsup hls) bot_le) (le_antisymm hls bot_le)

/-- Example 5.4, "by Theorem 3.3 every `μ`-random point has orbit complexity `0`": for every
oracle `A` admissible for `(ℕ^ℕ, d, σ, μ)` and every presentation whose ideal points have
`A`-computable symbols, every `μ`-random point relative to `A` is eventually `0`, has local
entropies `(0, 0)` and orbit complexities `K̲^A = K̄^A = 0`. Divergence: the hypothesis `hP`
(computable symbols, as in Proposition 7.10) is added; no presentation of Baire space is fixed in
the library, so it is not discharged here. Without it, see
`noteSupp_orbitComplexities_baireMeasure_fst` and
`noteSupp_exists_cone_orbitComplexities_baireMeasure`. Blueprint node `meas:examples`. -/
theorem noteSupp_orbitComplexities_baireMeasure_of_mem_randomPoints
    (P : Presentation (ℕ → ℕ)) (A : Set ℕ)
    (hA : IsMeasureAdmissible P shiftMap baireMeasure A)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) {x : ℕ → ℕ}
    (hx : x ∈ randomPoints P A baireMeasure) :
    (∀ᶠ i in atTop, x i = 0) ∧ localEntropy baireMeasure shiftMap x = (0, 0) ∧
      orbitComplexities P shiftMap A x = (0, 0) := by
  obtain ⟨N, hN, hsupp⟩ := noteSupp_baire_of_mem_randomPoints P A hA.1 hP hx
  have hloc := noteSupp_localEntropy_baireMeasure_of_eventually hN hsupp
  refine ⟨eventually_atTop.2 ⟨N, hN⟩, hloc, ?_⟩
  rw [orbitComplexities_eq_localEntropy P shiftMap continuous_shiftMap_baire A baireMeasure hA hx,
    hloc]


/-- Example 5.4, lower complexity, for every admissible oracle and every presentation: at every
`μ`-random point `K̲^A(x, σ) = 0` (Theorem 4.3(a): `sup_{R_A} K̲^A = ess sup h̲_μ = 0`).
Blueprint node `meas:examples`. -/
theorem noteSupp_orbitComplexities_baireMeasure_fst (P : Presentation (ℕ → ℕ)) (A : Set ℕ)
    (hA : IsMeasureAdmissible P shiftMap baireMeasure A) {x : ℕ → ℕ}
    (hx : x ∈ randomPoints P A baireMeasure) : (orbitComplexities P shiftMap A x).1 = 0 :=
  nonpos_iff_eq_zero.1 (noteSupp_orbitComplexities_fst_le_of_ae P shiftMap
    continuous_shiftMap_baire A baireMeasure hA
    (ae_localEntropy_baireMeasure.mono fun _ h ↦ by rw [h]) hx)

/-- Example 5.4 on a cone of oracles, for every presentation: there is an oracle `C` such that
for every `B ≥_T C` (all admissible) every `μ`-random point relative to `B` has orbit
complexities `(0, 0)`. Blueprint node `meas:examples`. -/
theorem noteSupp_exists_cone_orbitComplexities_baireMeasure (P : Presentation (ℕ → ℕ)) :
    ∃ C : Set ℕ, ∀ B : Set ℕ, charOracle C ≤ᵀ charOracle B →
      IsMeasureAdmissible P shiftMap baireMeasure B ∧
        ∀ x ∈ randomPoints P B baireMeasure, orbitComplexities P shiftMap B x = (0, 0) :=
  noteSupp_exists_cone_orbitComplexities_eq P shiftMap continuous_shiftMap_baire baireMeasure
    ae_localEntropy_baireMeasure

end baire

/-! ### Example 5.5: `z` and `z'` are computable from `0′` -/

section exampleFiveFive

/-- **Limit lemma** (Shoenfield, the direction used here): a sequence with computable
approximations `g t k → v k` (bitwise eventually constant) is computable from the halting
problem `0′`. Blueprint node `meas:examples`. -/
theorem noteSupp_computableInJump_of_limit {g : ℕ → ℕ → Bool} (hg : Computable₂ g)
    {v : ℕ → Bool} (hv : ∀ k, ∀ᶠ t in atTop, g t k = v k) : ComputableInJump v := by
  classical
  set p : ℕ × ℕ → ℕ → Bool := fun ks t ↦ decide (ks.2 ≤ t) && !decide (g t ks.1 = g ks.2 ks.1)
    with hp
  have hpc : Computable₂ p := by
    have h1 : Computable fun x : (ℕ × ℕ) × ℕ ↦ decide (x.1.2 ≤ x.2) :=
      (PrimrecRel.comp Primrec.nat_le (Primrec.snd.comp Primrec.fst) Primrec.snd).decide.to_comp
    have h2 : Computable fun x : (ℕ × ℕ) × ℕ ↦ decide (g x.2 x.1.1 = g x.1.2 x.1.1) :=
      primrec_decideEq.to_comp.comp (hg.comp Computable.snd (Computable.fst.comp Computable.fst))
        (hg.comp (Computable.snd.comp Computable.fst) (Computable.fst.comp Computable.fst))
    exact (Primrec.and.to_comp.comp h1 (Primrec.not.to_comp.comp h2)).to₂
  obtain ⟨h, hh, hspec⟩ := exists_computableInJump_semidecide hpc
  set f : ℕ → ℕ → Option Bool := fun k s ↦ cond (h (k, s)) none (some (g s k)) with hf
  have hfc : ComputableIn₂ {haltingChi} f :=
    computable_in_cond (c := fun q : ℕ × ℕ ↦ h q) hh (Computable.const none).computableIn
      (Computable.option_some.comp (hg.comp Computable.snd Computable.fst)).computableIn
  have hstab : ∀ k s, h (k, s) = false → g s k = v k := by
    intro k s hks
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hv k)
    have hns : ¬ ∃ t, p (k, s) t = true := fun hex ↦ by
      rw [← hspec] at hex; rw [hks] at hex; exact Bool.false_ne_true hex
    have := hT (max s T) (le_max_right _ _)
    by_contra hne
    exact hns ⟨max s T, by simp [hp, this, Ne.symm hne]⟩
  refine PartrecIn.of_eq_tot (PartrecIn.rfindOpt hfc) fun k ↦ ?_
  have hdom : (Nat.rfindOpt (f k)).Dom := by
    obtain ⟨T, hT⟩ := eventually_atTop.1 (hv k)
    refine Nat.rfindOpt_dom.2 ⟨T, g T k, ?_⟩
    have hT' : h (k, T) = false := by
      by_contra hne
      rw [Bool.not_eq_false, hspec] at hne
      obtain ⟨t, ht⟩ := hne
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not] at ht
      exact ht.2 ((hT t ht.1).trans (hT T le_rfl).symm)
    simp [hf, hT']
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 hdom
  obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hb
  have hs' : h (k, s) = false ∧ g s k = b := by
    cases hcs : h (k, s)
    · simp only [hf, hcs, Bool.cond_false, Option.mem_def, Option.some.injEq] at hs
      exact ⟨rfl, hs⟩
    · simp [hf, hcs] at hs
  rw [← hstab k s hs'.1, hs'.2]
  exact hb


/-- The halting oracle `0′` of `OracleComputability` (`haltingChi`) is the characteristic
oracle of the halting set. -/
lemma noteSupp_haltingChi_eq : haltingChi = charOracle {n | haltingSet n} := rfl

/-- The halting set computes `0′`: the hypothesis of the Example 5.5 statements is satisfiable. -/
lemma noteSupp_haltingOracle_le_halting : haltingOracle ≤ᵀ charOracle {n | haltingSet n} :=
  TuringReducible.refl _

/-- A `0′`-computable function is computable relative to every oracle `A` that computes `0′`
(`haltingOracle ≤ᵀ charOracle A`). -/
lemma noteSupp_computableIn_of_jump {α σ : Type*} [Primcodable α] [Primcodable σ] {f : α → σ}
    (hf : ComputableInJump f) {A : Set ℕ} (hA : haltingOracle ≤ᵀ charOracle A) :
    ComputableIn {charOracle A} f :=
  computableIn_mono_oracle (A := {n | haltingSet n}) hf hA

/-- A causal map given on prefixes by a computable word map sends `A`-computable sequences to
`A`-computable sequences. -/
lemma noteSupp_computableIn_of_wordMap {A : Set ℕ} {F : List Bool → List Bool}
    (hFc : Computable F) {f : (ℕ → Bool) → ℕ → Bool}
    (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) {w : ℕ → Bool}
    (hw : ComputableIn {charOracle A} w) : ComputableIn {charOracle A} (f w) := by
  have hpre := shiftTranslation_computableIn_wordPrefix (A := A) (f := fun _ i ↦ w i)
    (hw.comp Computable.snd.computableIn)
  have hpre' : ComputableIn {charOracle A} fun j : ℕ ↦ wordPrefix w (j + 1) :=
    hpre.comp ((Computable.const 0).pair Computable.succ).computableIn
  refine ((Primrec.list_getD false).to_comp.computableIn.comp
    ((hFc.computableIn.comp hpre').pair ComputableIn.id)).of_eq fun j ↦ ?_
  rw [← hF]
  exact ex55u_getD_wordPrefix _ (Nat.lt_succ_self j)

end exampleFiveFive

section witnesses

attribute [local instance] cantorMetricSpace

/-- Example 5.5, last sentence, for part (1): the measure `μ = λ ∘ f⁻¹` and the point
`z = f(Ω)` of `ExampleFiveFiveUpper` (with `Ω` Chaitin's `Ω`) satisfy everything stated in
`exists_countable_atomic_random_upperLocalEntropy_eq_one'` (`μ` is a probability measure
admissible for `cantorPresentation`, here for every oracle, carried by a countable set, and `z`
is `μ`-random with `h̄_μ(σ, z) = 1`), and moreover `z` is not an atom, `z` is computable from the
halting problem `0′`, and `z` is not `μ`-random relative to any oracle `A` that computes `0′`
("so it stops being random once the oracle computes it"). Blueprint node `meas:examples`. -/
theorem noteSupp_exampleFiveFive_upper_not_random_of_jump :
    ∃ μ : Measure (ℕ → Bool), IsProbabilityMeasure μ ∧
      (∀ A, IsMeasureAdmissible cantorPresentation shiftMap μ A) ∧
      (∃ S : Set (ℕ → Bool), S.Countable ∧ μ Sᶜ = 0) ∧
      ∃ z ∈ randomPoints cantorPresentation ∅ μ, (localEntropy μ shiftMap z).2 = 1 ∧
        μ {z} = 0 ∧ ComputableInJump z ∧
        ∀ A : Set ℕ, haltingOracle ≤ᵀ charOracle A → z ∉ randomPoints cantorPresentation A μ := by
  obtain ⟨w, b, hw, hbc, hb⟩ := ex55u_exists_approx
  have hFc := ex55u_computable_F hbc
  have hF : ∀ y n, wordPrefix (ex55u_f b y) n = ex55u_F b (wordPrefix y n) :=
    ex55u_wordPrefix_f
  have hmeas := cantorPres_measurable hF
  have hae : ∀ᵐ y ∂uniformMeasure, y ≠ w := by
    rw [ae_iff]
    simpa using uniformMeasure_singleton w
  have hent : (localEntropy (uniformMeasure.map (ex55u_f b)) shiftMap (ex55u_f b w)).2 = 1 :=
    le_antisymm (localEntropy_map_uniformMeasure_le_one hmeas.aemeasurable
      (cantorPres_causal hF) w).2 (ex55u_one_le hb)
  have hatom : uniformMeasure.map (ex55u_f b) {ex55u_f b w} = 0 := by
    by_contra h
    have := localEntropy_eq_zero_of_measure_singleton_ne_zero _ shiftMap h
    rw [this] at hent
    exact zero_ne_one hent
  have hjump : ComputableInJump (ex55u_f b w) :=
    noteSupp_computableIn_of_wordMap hFc hF (noteSupp_computableInJump_of_limit hbc hb)
  refine ⟨uniformMeasure.map (ex55u_f b), inferInstance,
    fun A ↦ cantorPres_isMeasureAdmissible_map_uniformMeasure A hFc hF,
    exists_countable_map_compl_eq_zero _ hmeas.aemeasurable
      (hae.mono fun y hy ↦ ex55u_eventually_false hb hy),
    ex55u_f b w, cantorPres_map_mem_randomPoints_of_isMartinLofRandom hFc hF hw, hent, hatom,
    hjump, fun A hA ↦ ?_⟩
  exact noteSupp_not_mem_randomPoints_of_computableIn _
    (cantorPres_isComputableWordMeasureIn_map hFc hF _
      (cantorPres_isComputableWordMeasureIn_uniformMeasure A))
    (noteSupp_computableIn_of_jump hjump hA) hatom

/-- Example 5.5, last sentence, for part (2): the measure `μ' = λ ∘ f'⁻¹` and the point
`z' = f'(Ω)` of `ExampleFiveFiveLower` satisfy everything stated in
`exists_random_lowerLocalEntropy_eq_zero'` (admissibility here for every oracle,
`Φ_{μ'} = (1, 1)` a.e., `z'` is `μ'`-random with `h̲_{μ'}(σ, z') = 0`), and moreover `z'` is not
an atom, `z'` is computable from `0′`, and `z'` is not `μ'`-random relative to any oracle that
computes `0′`. Blueprint node `meas:examples`. -/
theorem noteSupp_exampleFiveFive_lower_not_random_of_jump :
    ∃ μ' : Measure (ℕ → Bool), IsProbabilityMeasure μ' ∧
      (∀ A, IsMeasureAdmissible cantorPresentation shiftMap μ' A) ∧
      (∀ᵐ x ∂μ', localEntropy μ' shiftMap x = (1, 1)) ∧
      ∃ z' ∈ randomPoints cantorPresentation ∅ μ', (localEntropy μ' shiftMap z').1 = 0 ∧
        μ' {z'} = 0 ∧ ComputableInJump z' ∧
        ∀ A : Set ℕ, haltingOracle ≤ᵀ charOracle A →
          z' ∉ randomPoints cantorPresentation A μ' := by
  obtain ⟨Ω, W, hΩ, hW, hconv⟩ := ex55l_exists_omega
  have hF := ex55l_wordPrefix_f W
  have hFc := ex55l_computable_F hW
  have hae := ex55l_ae_localEntropy_eq_one W hconv
  have hent : (localEntropy (uniformMeasure.map (ex55l_f W)) shiftMap (ex55l_f W Ω)).1 = 0 := by
    rw [localEntropy_shiftMap (by norm_num) (by norm_num) (fun _ _ ↦ cantorMetricSpace_dist_eq)]
    exact ex55l_liminf_eq_zero W hconv
  have hatom : uniformMeasure.map (ex55l_f W) {ex55l_f W Ω} = 0 := by
    by_contra h
    have hmem : ex55l_f W Ω ∈ {x | localEntropy (uniformMeasure.map (ex55l_f W)) shiftMap x =
        (1, 1)} := by
      by_contra hn
      exact h (measure_mono_null (singleton_subset_iff.2 hn) (ae_iff.1 hae))
    rw [mem_ofPred_eq] at hmem
    rw [hmem] at hent
    exact one_ne_zero hent
  have hjump : ComputableInJump (ex55l_f W Ω) :=
    noteSupp_computableIn_of_wordMap hFc hF (noteSupp_computableInJump_of_limit hW hconv)
  refine ⟨uniformMeasure.map (ex55l_f W), inferInstance,
    fun A ↦ cantorPres_isMeasureAdmissible_map_uniformMeasure A hFc hF, hae, ex55l_f W Ω,
    cantorPres_map_mem_randomPoints_of_isMartinLofRandom hFc hF hΩ, hent, hatom, hjump,
    fun A hA ↦ ?_⟩
  exact noteSupp_not_mem_randomPoints_of_computableIn _
    (cantorPres_isComputableWordMeasureIn_map hFc hF _
      (cantorPres_isComputableWordMeasureIn_uniformMeasure A))
    (noteSupp_computableIn_of_jump hjump hA) hatom

end witnesses

end Kolmogorov.PointToSet
