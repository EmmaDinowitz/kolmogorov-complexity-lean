/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupPoincare

/-!
# Effective upper Birkhoff bound for bounded lower semicomputable functions

Part of Theorem 3.3 of Hoyrup (STACS 2012), in the only form needed here: for an `A`-computable
shift-invariant ergodic probability measure `ν` on `ℕ → Bool`, a bounded function `v` that is lower
semicomputable relative to `A`, and a sequence `ω` that is `ν`-random relative to `A`,
`limsup_n (1/n) ∑_{k<n} v(σ^k ω) ≤ ∫ v dν`.

Proof. For rational `q > ∫ v` and `K`, the set `C_K = {x | ∀ n ≥ K, A_n v(x) ≤ q}` has an `A`-c.e.
complement (`IsLscFunIn.shiftAverage`), and by Birkhoff's theorem for the bounded measurable
function `v` (`Ergodic.ae_tendsto_birkhoffAverage`) `ν(C_K) > 0` for some `K`. By effective
Poincaré recurrence (`exists_iterate_notMem_of_mem_wordRandomPoints`) some tail `σ^m ω` lies in
`C_K`, and since `v` is bounded the first `m` terms do not change the `limsup`.

Blueprint node `erg:hoyrup`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-- Birkhoff averages of a function bounded by `B` are bounded by `B`. -/
private theorem shiftAverage_le_of_le {v : (ℕ → Bool) → ℝ≥0∞} {B : ℝ≥0∞}
    (hvB : ∀ x, v x ≤ B) (n : ℕ) (x : ℕ → Bool) : shiftAverage v n x ≤ B := by
  refine ENNReal.div_le_of_le_mul ?_
  calc ∑ k ∈ Finset.range n, v (shiftMap^[k] x)
      ≤ (Finset.range n).card • B := Finset.sum_le_card_nsmul _ _ _ fun k _ ↦ hvB _
    _ = B * n := by rw [Finset.card_range, nsmul_eq_mul, mul_comm]

/-- For a finite-valued `v`, the `ℝ≥0∞` Birkhoff average is the real Birkhoff average of
`toReal ∘ v`. -/
private theorem toReal_shiftAverage {v : (ℕ → Bool) → ℝ≥0∞} (hfin : ∀ x, v x ≠ ⊤) (n : ℕ)
    (x : ℕ → Bool) :
    (shiftAverage v n x).toReal = birkhoffAverage ℝ shiftMap (fun y ↦ (v y).toReal) n x := by
  rw [shiftAverage, ENNReal.toReal_div, ENNReal.toReal_sum fun k _ ↦ hfin _, birkhoffAverage,
    birkhoffSum, smul_eq_mul, div_eq_inv_mul, ENNReal.toReal_natCast]

/-- If, after `m` steps, all Birkhoff averages of length `≥ K + 1` are at most `q`, then the
`limsup` of the Birkhoff averages is at most `q` (the first `m` terms are bounded by `B`). -/
private theorem limsup_shiftAverage_le_of_iterate {v : (ℕ → Bool) → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hvB : ∀ x, v x ≤ B) {ω : ℕ → Bool} {q : ℝ≥0∞} {m K : ℕ}
    (h : ∀ n, shiftAverage v (K + n) (shiftMap^[m] ω) ≤ q) :
    limsup (fun n ↦ shiftAverage v n ω) atTop ≤ q := by
  rw [← Filter.limsup_nat_add _ (m + K + 1)]
  have hbound : ∀ i, shiftAverage v (i + (m + K + 1)) ω
      ≤ (m : ℝ≥0∞) * B * ((i + (m + K + 1) : ℕ) : ℝ≥0∞)⁻¹ + q := by
    intro i
    set N := i + (m + K + 1) with hN
    have hNm : N = m + (K + (i + 1)) := by omega
    have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hsplit : ∑ k ∈ Finset.range N, v (shiftMap^[k] ω) =
        ∑ k ∈ Finset.range m, v (shiftMap^[k] ω) +
          ∑ k ∈ Finset.range (K + (i + 1)), v (shiftMap^[k] (shiftMap^[m] ω)) := by
      rw [hNm, Finset.sum_range_add]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [add_comm, Function.iterate_add_apply]
    have h1 : ∑ k ∈ Finset.range m, v (shiftMap^[k] ω) ≤ m * B := by
      calc ∑ k ∈ Finset.range m, v (shiftMap^[k] ω)
          ≤ (Finset.range m).card • B := Finset.sum_le_card_nsmul _ _ _ fun k _ ↦ hvB _
        _ = m * B := by rw [Finset.card_range, nsmul_eq_mul]
    have h2 : ∑ k ∈ Finset.range (K + (i + 1)), v (shiftMap^[k] (shiftMap^[m] ω))
        ≤ q * N := by
      have := h (i + 1)
      rw [shiftAverage, ENNReal.div_le_iff (Nat.cast_ne_zero.2 (by omega))
        (ENNReal.natCast_ne_top _)] at this
      exact this.trans (by gcongr; omega)
    refine ENNReal.div_le_of_le_mul ?_
    rw [hsplit, add_mul, mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _),
      mul_one]
    exact add_le_add h1 h2
  have htend : Tendsto (fun i : ℕ ↦ (m : ℝ≥0∞) * B * ((i + (m + K + 1) : ℕ) : ℝ≥0∞)⁻¹ + q)
      atTop (𝓝 q) := by
    have h0 : Tendsto (fun i : ℕ ↦ ((i + (m + K + 1) : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat _)
    have := (ENNReal.Tendsto.const_mul h0
      (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hB))).add_const q
    simpa using this
  calc limsup (fun i ↦ shiftAverage v (i + (m + K + 1)) ω) atTop
      ≤ limsup (fun i : ℕ ↦ (m : ℝ≥0∞) * B * ((i + (m + K + 1) : ℕ) : ℝ≥0∞)⁻¹ + q) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound)
    _ = q := htend.limsup_eq

/-- Effective upper Birkhoff bound: `limsup_n A_n v(ω) ≤ ∫ v dν` for a bounded lower semicomputable
`v` at every `ν`-random sequence. Blueprint node `erg:hoyrup`. -/
theorem limsup_shiftAverage_le_lintegral {A : Set ℕ} {ν : Measure (ℕ → Bool)}
    [IsProbabilityMeasure ν] (hν : Ergodic shiftMap ν) (hc : IsComputableWordMeasureIn A ν)
    {v : (ℕ → Bool) → ℝ≥0∞} (hv : IsLscFunIn A v) {B : ℝ≥0∞} (hB : B ≠ ⊤) (hvB : ∀ x, v x ≤ B)
    {ω : ℕ → Bool} (hω : ω ∈ wordRandomPoints A ν) :
    limsup (fun n ↦ shiftAverage v n ω) atTop ≤ ∫⁻ x, v x ∂ν := by
  have hmeas := hv.measurable
  have hfin : ∀ x, v x ≠ ⊤ := fun x ↦ ne_top_of_le_ne_top hB (hvB x)
  refine le_of_forall_gt_imp_ge_of_dense fun c hc' ↦ ?_
  obtain ⟨q, -, hIq, hqc⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc'
  change _ < ENNReal.ofReal q at hIq
  refine le_trans ?_ hqc.le
  change _ ≤ ENNReal.ofReal q
  obtain ⟨E, hE, hEq⟩ := hv.shiftAverage
  set C : ℕ → Set (ℕ → Bool) :=
    fun K ↦ {x | ∀ n, shiftAverage v (K + n) x ≤ ENNReal.ofReal q} with hC
  -- Birkhoff's theorem: some `C K` has positive measure.
  have hpos : ∃ K, 0 < ν (C K) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    have hint : ∫ y, (v y).toReal ∂ν < q := by
      rw [integral_toReal hmeas.aemeasurable (ae_of_all _ fun x ↦ lt_top_iff_ne_top.2 (hfin x))]
      exact ENNReal.toReal_lt_of_lt_ofReal hIq
    have hae : ∀ᵐ x ∂ν, x ∈ ⋃ K, C K := by
      filter_upwards [Ergodic.ae_tendsto_birkhoffAverage hν hmeas.ennreal_toReal
        (C := B.toReal) fun x ↦ by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.toReal_mono hB (hvB x)] with x hx
      obtain ⟨K, hK⟩ := eventually_atTop.1 (hx.eventually (gt_mem_nhds hint))
      refine mem_iUnion.2 ⟨K, fun n ↦ ?_⟩
      have := hK (K + n) (Nat.le_add_right _ _)
      rw [← toReal_shiftAverage hfin] at this
      rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hB (shiftAverage_le_of_le hvB _ _))]
      exact ENNReal.ofReal_le_ofReal this.le
    intro h0
    have h1 : ν (⋃ K, C K)ᶜ = 0 := ae_iff.1 hae
    have := measure_union_null h0 h1
    rw [union_compl_self, measure_univ] at this
    exact one_ne_zero this
  obtain ⟨K, hK⟩ := hpos
  -- The complement of `C K` is an `A`-c.e. union of cylinders.
  have hE' : IsREIn A fun w : List Bool ↦ ∃ n, E ((K + n, q), w) := by
    refine IsREIn.exists (F := fun p : List Bool × ℕ ↦ E ((K + p.2, q), p.1)) ?_
    refine hE.comp (f := fun p : List Bool × ℕ ↦ ((K + p.2, q), p.1)) ?_
    refine Computable.computableIn ?_
    exact ((((Primrec.nat_add.comp (Primrec.const K) Primrec.snd)).pair
      (Primrec.const q)).pair Primrec.fst).to_comp
  have hset : (⋃ w ∈ {w | ∃ n, E ((K + n, q), w)}, listCylinder w) = (C K)ᶜ := by
    ext x
    have key : ∀ n, (x ∈ ⋃ w ∈ {w | E ((K + n, q), w)}, listCylinder w) ↔
        ENNReal.ofReal q < shiftAverage v (K + n) x := fun n ↦ by
      rw [← hEq (K + n) q]; rfl
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop, hC, mem_compl_iff, not_forall,
      not_le] at key ⊢
    constructor
    · rintro ⟨w, ⟨n, hn⟩, hx⟩; exact ⟨n, (key n).1 ⟨w, hn, hx⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨w, hw, hx⟩ := (key n).2 hn
      exact ⟨w, ⟨n, hw⟩, hx⟩
  obtain ⟨m, hm⟩ := exists_iterate_notMem_of_mem_wordRandomPoints hν hc hE'
    (by rwa [hset, compl_compl]) hω
  rw [hset, notMem_compl_iff] at hm
  exact limsup_shiftAverage_le_of_iterate hB hvB hm

end Kolmogorov.PointToSet
