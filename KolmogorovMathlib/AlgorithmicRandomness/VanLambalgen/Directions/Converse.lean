/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Pullback
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.Trim

/-!
# van Lambalgen: relatively random coordinates make a random pair

`IsMartinLofRandomIn.cantorJoin` (blueprint node `vl:converse`): if `x` is random for `μ` relative
to `A`, `y` is random for `ν` relative to `A ⊕ x` and `ν` is computable relative to `A`, then
`x ⊕ y` is random for `joinMeasure μ ν` relative to `A`. No hypothesis on `μ`.

Let `W` be a test relative to `A` for `joinMeasure μ ν` containing `x ⊕ y`. Its sections
`S^z_m = {y' | z ⊕ y' ∈ W_m}` form a family oracle-uniform relative to `A`
(`uniformFamily_sectionEnum`). Trim it uniformly in the oracle (`trimUniform`) at the level
`m = 2L + 3` with trimming level `L`, and let `D_L` be the oracles at which something is
discarded (`discardSet`). Each `z ∈ D_L` has `ν(S^z_{2L+3}) > 2^{-(L+2)}`, so by Markov's
inequality and Fubini (`joinMeasure_jointSet`)
`2^{-(L+2)} μ(D_L) ≤ ∫⁻ z, ν(S^z_{2L+3}) ∂μ = joinMeasure μ ν (W_{2L+3}) ≤ 2^{-(2L+3)}`, that is
`μ(D_L) ≤ 2^{-(L+1)}`. The sets `V_k = ⋃_L D_{L+k+1}` form a test relative to `A` for `μ`, so
`x ∉ V_k` for some `k`. Then at `x` nothing is discarded at the levels `L = n + k + 1`, and the
trimmed sections `Y_n`, which are effectively open relative to `A ⊕ x`, satisfy
`ν(Y_n) ≤ 2^{-(n+k+1)}` and `Y_n = S^x_{2L+3} ∋ y`: a test that `y` fails.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal
open PointToSet (oracleJoin)

variable {A : Set ℕ} {μ ν : Measure CantorSeq} {x y : CantorSeq}

/-- Unions over a computable family of levels of a uniformly effectively open family are
uniformly effectively open. -/
private theorem isUniformlyEffectiveOpenIn_iUnion {D : ℕ → Set CantorSeq}
    (hD : IsUniformlyEffectiveOpenIn A D) {r : ℕ → ℕ → ℕ} (hr : Computable₂ r) :
    IsUniformlyEffectiveOpenIn A fun k => ⋃ L, D (r k L) := by
  obtain ⟨d, hd, hdD⟩ := hD
  have hu : Computable fun p : ℕ × ℕ => Nat.unpair p.2 := Computable.unpair.comp Computable.snd
  refine ⟨fun k s => d (r k (Nat.unpair s).1) (Nat.unpair s).2,
    ComputableIn.of_eq (hd.comp (hr.comp Computable.fst (Computable.fst.comp hu)).computableIn
      (Computable.snd.comp hu).computableIn) fun _ => rfl, fun k => ?_⟩
  ext w
  simp only [Set.mem_iUnion, hdD]
  constructor
  · rintro ⟨L, i, h⟩
    exact ⟨Nat.pair L i, by simpa using h⟩
  · rintro ⟨s, h⟩
    exact ⟨(Nat.unpair s).1, (Nat.unpair s).2, h⟩

/-- If `x` is random for `μ` relative to `A` and `y` is random for `ν` relative to `A ⊕ x`, then
the interleaving `x ⊕ y` is random for `joinMeasure μ ν` relative to `A`.
Blueprint node `vl:converse`. -/
theorem IsMartinLofRandomIn.cantorJoin (hν : IsComputableCantorMeasureIn A ν)
    (hx : IsMartinLofRandomIn A μ x) (hy : IsMartinLofRandomIn (oracleJoin A (seqOracle x)) ν y) :
    IsMartinLofRandomIn A (joinMeasure μ ν) (cantorJoin x y) := by
  have := hν.isFiniteMeasure
  intro W hW hxyW
  obtain ⟨f, hf, hfW⟩ := hW.1
  obtain ⟨a, ha, hacc⟩ := hν
  have hg := isOracleUniformIn_sectionEnum hf
  have hsec : ∀ z m,
      uniformFamily (sectionEnum f) z m = {y' | Kolmogorov.cantorJoin z y' ∈ W m} :=
    fun z m => by rw [uniformFamily_sectionEnum, ← hfW m]
  -- The discard sets have small `μ`-measure.
  have hDm : ∀ L,
      μ (discardSet a (sectionEnum f) (2 * L + 3) L) ≤ (2 : ℝ≥0∞)⁻¹ ^ (L + 1) := by
    intro L
    have hjoint : jointSet (fun z => uniformFamily (sectionEnum f) z (2 * L + 3)) =
        W (2 * L + 3) := by
      simp only [hsec]
      exact jointSet_sections _
    have hmeas : MeasurableSet (W (2 * L + 3)) := hW.1.measurableSet _
    have hmeasJ : MeasurableSet (jointSet fun z =>
        uniformFamily (sectionEnum f) z (2 * L + 3)) := hjoint ▸ hmeas
    have hint : ∫⁻ z, ν (uniformFamily (sectionEnum f) z (2 * L + 3)) ∂μ ≤
        (2 : ℝ≥0∞)⁻¹ ^ (2 * L + 3) := by
      rw [← joinMeasure_jointSet hmeasJ, hjoint, ← dyadicValue_one_eq_inv_two_pow']
      exact hW.2 _
    have hF : Measurable fun z => ν (uniformFamily (sectionEnum f) z (2 * L + 3)) := by
      have hpre : MeasurableSet ((fun p : CantorSeq × CantorSeq =>
          Kolmogorov.cantorJoin p.1 p.2) ⁻¹' W (2 * L + 3)) := measurable_cantorJoin hmeas
      have hfun : (fun z => ν (uniformFamily (sectionEnum f) z (2 * L + 3))) = fun z =>
          ν (Prod.mk z ⁻¹' ((fun p : CantorSeq × CantorSeq =>
            Kolmogorov.cantorJoin p.1 p.2) ⁻¹' W (2 * L + 3))) := by
        funext z
        rw [hsec]
        rfl
      rw [hfun]
      exact measurable_measure_prodMk_left hpre
    have hsub : discardSet a (sectionEnum f) (2 * L + 3) L ⊆
        {z | (2 : ℝ≥0∞)⁻¹ ^ (L + 2) ≤ ν (uniformFamily (sectionEnum f) z (2 * L + 3))} :=
      fun z hz => (lt_measure_of_mem_discardSet hacc hz).le
    have hmarkov := (mul_meas_ge_le_lintegral₀ hF.aemeasurable ((2 : ℝ≥0∞)⁻¹ ^ (L + 2))).trans
      hint
    have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (2 * L + 3) =
        (2 : ℝ≥0∞)⁻¹ ^ (L + 2) * (2 : ℝ≥0∞)⁻¹ ^ (L + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit] at hmarkov
    refine (measure_mono hsub).trans ?_
    exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 hmarkov
  -- A test relative to `A` for `μ` made of discard sets.
  have hDo := isUniformlyEffectiveOpenIn_discardSet ha hg
  have hr : Computable₂ fun k L : ℕ => Nat.pair (2 * (L + k + 1) + 3) (L + k + 1) := by
    have hl : Primrec fun p : ℕ × ℕ => p.2 + p.1 + 1 :=
      Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd Primrec.fst) (Primrec.const 1)
    exact (Primrec₂.natPair.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hl) (Primrec.const 3)) hl).to_comp
  have hVo : IsUniformlyEffectiveOpenIn A fun k =>
      ⋃ L, discardSet a (sectionEnum f) (2 * (L + k + 1) + 3) (L + k + 1) := by
    simpa only [Nat.unpair_pair] using isUniformlyEffectiveOpenIn_iUnion hDo hr
  have hVm : ∀ k, μ (⋃ L, discardSet a (sectionEnum f) (2 * (L + k + 1) + 3) (L + k + 1)) ≤
      dyadicValue 1 k := by
    intro k
    refine (measure_iUnion_le _).trans ?_
    calc ∑' L, μ (discardSet a (sectionEnum f) (2 * (L + k + 1) + 3) (L + k + 1))
        ≤ ∑' L, (2 : ℝ≥0∞)⁻¹ ^ (k + 1 + L + 1) :=
          ENNReal.tsum_le_tsum fun L => (hDm (L + k + 1)).trans_eq (by ring_nf)
      _ = (2 : ℝ≥0∞)⁻¹ ^ (k + 1) := tsum_inv_two_pow_shift (k + 1)
      _ ≤ dyadicValue 1 k := by
          rw [dyadicValue_one_eq_inv_two_pow']
          exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 (by norm_num)) (by omega)
  obtain ⟨k, hk⟩ :
      ∃ k, x ∉ ⋃ L, discardSet a (sectionEnum f) (2 * (L + k + 1) + 3) (L + k + 1) := by
    by_contra hall
    push Not at hall
    exact hx _ ⟨hVo, hVm⟩ (Set.mem_iInter.2 hall)
  simp only [Set.mem_iUnion, not_exists] at hk
  -- The trimmed sections at `x` form a test relative to `A ⊕ x` that `y` fails.
  have hr' : Computable fun n : ℕ => Nat.pair (2 * (n + k + 1) + 3) (n + k + 1) :=
    hr.comp (Computable.const k) Computable.id
  have hYo := ((isOracleUniformIn_trimUniform ha hg).reindex
    hr').isUniformlyEffectiveOpenIn_uniformFamily x
  refine hy _ ⟨hYo, fun n => ?_⟩ (Set.mem_iInter.2 fun n => ?_)
  · change ν (uniformFamily (trimUniform a (sectionEnum f)) x
      (Nat.pair (2 * (n + k + 1) + 3) (n + k + 1))) ≤ dyadicValue 1 n
    refine (measure_uniformFamily_trimUniform_le hacc _ x _ _).trans ?_
    rw [dyadicValue_one_eq_inv_two_pow', dyadicValue_one_eq_inv_two_pow']
    exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 (by norm_num)) (by omega)
  · change y ∈ uniformFamily (trimUniform a (sectionEnum f)) x
      (Nat.pair (2 * (n + k + 1) + 3) (n + k + 1))
    rw [uniformFamily_trimUniform_of_not_mem (hk n), hsec]
    exact Set.mem_iInter.1 hxyW _

end Kolmogorov
