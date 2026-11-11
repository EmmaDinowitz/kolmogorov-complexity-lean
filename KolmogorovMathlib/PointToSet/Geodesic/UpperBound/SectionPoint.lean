/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.PrecisionChain
import KolmogorovMathlib.Oracle.PrefixComplexity.NatBounds

/-!
# Flow coordinate and the upper section-point bound (Chapter I, part 3)

The nodes `geo:flow-coordinate` and `geo:section-point-upper` of
`geodesic_upper_bound_blueprint.md`. `EffectiveGeodesicData.flow_coordinate` restores the flow
coordinate: for `|t₀| ≤ a` and `z = φ t₀ x`, `Dim^A(x) ≤ 1 + Dim^A(z)` and
`dim^A(x) ≤ 1 + dim^A(z)` for every `A` above `B` (a `B`-partial recursive decoder recovers
`x` from a name of `z` and a dyadic approximation of `-t₀`). `sectionPoint_upper` is the upper
bound `Dim^A(x) ≤ 1 + Dim^A_BS(x,f,u⁺) + Dim^A_BS(x,f⁻¹,u⁻)`, obtained from the precision chain
along the stopping times with the flow coordinate restored at every stage.
-/

namespace Kolmogorov.PointToSet

open Filter Set
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [CompactSpace X]

section limits

variable {G : GeodesicReconstructionData X} (P : Presentation X) {A : Set ℕ}

/-! ### `geo:flow-coordinate` -/

/-- Restoring the flow coordinate (PO §4.2 step 6): for `|t₀| ≤ a` and `z = φ t₀ x`,
`Dim^A(x) ≤ 1 + Dim^A(z)` and `dim^A(x) ≤ 1 + dim^A(z)`, for every `A` above `B`.
Proof: from an ideal `i` within `δ = 2^{-m}` of `z` and the dyadic `q = k 2^{-m} - N` within `δ`
of `-t₀` (`N = ⌈a⌉₊ + 1`, `k ≤ 2N 2^m`), a `B`-partial recursive decoder finds (through the sound
and complete relation of the represented flow, `E.flow_represented`) an ideal point within `δ`
of `φ q (ι i)`, which is within `(1 + L^N + V) δ` of `x`; so
`K^A_{(1+L^N+V)δ}(x) ≤ K^A_δ(z) + K^A(k, m) + O(1) ≤ K^A_δ(z) + m + O(log m)`
(`oracleNatComplexity_le_of_decoder`, `oracle_tuple_bounds_overhead`,
`oracleNatComplexity_le_log_add_loglog`). Divide by `-log₂((1+L^N+V)δ) = m - O(1)` and use
`dimension_along_scales(_upper)` along both geometric scale sequences.
Blueprint node `geo:flow-coordinate`. -/
theorem EffectiveGeodesicData.flow_coordinate {B : Set ℕ} (E : EffectiveGeodesicData G P B)
    (hBA : charOracle B ≤ᵀ charOracle A) {x : X} {t₀ a : ℝ} (ha : |t₀| ≤ a) :
    (staticPointDimensions P A x).2 ≤ 1 + (staticPointDimensions P A (G.φ t₀ x)).2 ∧
      (staticPointDimensions P A x).1 ≤ 1 + (staticPointDimensions P A (G.φ t₀ x)).1 := by
  classical
  set z := G.φ t₀ x with hz
  have hxz : x = G.φ (-t₀) z := by
    rw [hz, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  obtain ⟨R, hR, hsound, hcomp⟩ := E.flow_represented
  obtain ⟨qd, hqd, hqderr⟩ := E.presentation
  have hL1 := G.one_le_L
  have hL0 : 0 ≤ G.L := by linarith
  have hV0 := G.V_nonneg
  set N : ℕ := ⌈a⌉₊ + 1 with hN
  have haN : a + 1 ≤ N := by
    rw [hN]; push_cast; linarith [Nat.le_ceil a]
  have ha0 : 0 ≤ a := (abs_nonneg t₀).trans ha
  -- Lipschitz bound of the flow over times `|s| ≤ n`
  have hLip : ∀ n : ℕ, ∀ s : ℝ, |s| ≤ n → ∀ y y' : X,
      dist (G.φ s y) (G.φ s y') ≤ G.L ^ n * dist y y' := by
    intro n
    induction n with
    | zero =>
      intro s hs y y'
      have hs0 : s = 0 := by
        rw [Nat.cast_zero] at hs
        exact abs_nonpos_iff.mp hs
      subst hs0
      simp
    | succ n ih =>
      intro s hs y y'
      push_cast at hs
      set s₂ : ℝ := max (-1) (min 1 s) with hs₂
      have h2 : |s₂| ≤ 1 := by
        rw [abs_le]
        exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
      have h1 : |s - s₂| ≤ n := by
        rw [abs_le] at hs ⊢
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        rcases le_total s 1 with hs1 | hs1
        · rcases le_total (-1) s with hsm | hsm
          · have : s₂ = s := by rw [hs₂, min_eq_right hs1, max_eq_right hsm]
            rw [this, sub_self]
            constructor <;> linarith
          · have : s₂ = -1 := by rw [hs₂, min_eq_right hs1, max_eq_left hsm]
            rw [this]
            constructor <;> linarith
        · have : s₂ = 1 := by rw [hs₂, min_eq_left hs1, max_eq_right (by linarith)]
          rw [this]
          constructor <;> linarith
      have e : ∀ w : X, G.φ s w = G.φ s₂ (G.φ (s - s₂) w) := fun w ↦ by
        rw [← Flow.map_add]
        congr 1
        ring
      rw [e y, e y', pow_succ']
      calc dist (G.φ s₂ (G.φ (s - s₂) y)) (G.φ s₂ (G.φ (s - s₂) y'))
          ≤ G.L * dist (G.φ (s - s₂) y) (G.φ (s - s₂) y') := G.lipschitz_unit s₂ h2 _ _
        _ ≤ G.L * (G.L ^ n * dist y y') := by gcongr; exact ih (s - s₂) h1 y y'
        _ = G.L * G.L ^ n * dist y y' := by ring
  set Cfc : ℝ := 1 + G.L ^ N + G.V with hCfc
  have hLN : 1 ≤ G.L ^ N := one_le_pow₀ hL1
  have hCfc1 : 1 ≤ Cfc := by rw [hCfc]; linarith
  have hCfc0 : 0 < Cfc := by linarith
  set cL : ℝ := Real.logb 2 Cfc with hcL
  have hcL0 : 0 ≤ cL := Real.logb_nonneg one_lt_two hCfc1
  /- The decoder. -/
  have hpow : Computable fun m : ℕ ↦ (2 : ℚ)⁻¹ ^ m := by
    have h : Computable fun m : ℕ ↦ (Nat.rec (1 : ℚ) (fun _ ih ↦ (2 : ℚ)⁻¹ * ih) m : ℚ) :=
      Computable.nat_rec (f := fun m : ℕ ↦ m) (g := fun _ : ℕ ↦ (1 : ℚ))
        (h := fun _ p ↦ (2 : ℚ)⁻¹ * p.2) Computable.id (Computable.const 1)
        (computable₂_ratMul.comp (Computable.const (2 : ℚ)⁻¹) (Computable.snd.comp Computable.snd))
    refine h.of_eq fun m ↦ ?_
    induction m with
    | zero => simp
    | succ n ih => rw [pow_succ', ← ih]
  obtain ⟨qk, hqk_def⟩ : ∃ qk : ℕ × ℕ → ℚ,
      qk = fun km ↦ (km.1 : ℚ) * (2 : ℚ)⁻¹ ^ km.2 - (N : ℚ) := ⟨_, rfl⟩
  have hqk : Computable qk := by
    rw [hqk_def]
    exact computable₂_ratSub.comp (computable₂_ratMul.comp
      (ComputableReals.computable_natCastRat.comp Computable.fst) (hpow.comp Computable.snd))
      (Computable.const _)
  -- membership of ideal points in basic balls is semidecidable
  have hmem : IsREIn B fun ib : ℕ × (ℕ × ℚ) ↦ P.ι ib.1 ∈ basicBall P ib.2 := by
    have hcert : IsREIn B fun ibn : (ℕ × (ℕ × ℚ)) × ℕ ↦
        qd ((ibn.1.1, ibn.1.2.1), ibn.2) + (2 : ℚ)⁻¹ ^ ibn.2 < ibn.1.2.2 := by
      have hg : Computable fun ibn : (ℕ × (ℕ × ℚ)) × ℕ ↦ ((ibn.1.1, ibn.1.2.1), ibn.2) :=
        ((Computable.fst.comp Computable.fst).pair
          (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair Computable.snd
      have h1 : ComputableIn {charOracle B} fun ibn : (ℕ × (ℕ × ℚ)) × ℕ ↦
          qd ((ibn.1.1, ibn.1.2.1), ibn.2) := hqd.comp hg.computableIn
      have h2 : Computable fun ibn : (ℕ × (ℕ × ℚ)) × ℕ ↦ (2 : ℚ)⁻¹ ^ ibn.2 :=
        hpow.comp Computable.snd
      have h3 : ComputableIn {charOracle B} fun ibn : (ℕ × (ℕ × ℚ)) × ℕ ↦
          qd ((ibn.1.1, ibn.1.2.1), ibn.2) + (2 : ℚ)⁻¹ ^ ibn.2 :=
        computable₂_ratAdd.computableIn₂.comp h1 h2.computableIn
      have h4 : Computable fun ibn : (ℕ × (ℕ × ℚ)) × ℕ ↦ ibn.1.2.2 :=
        Computable.snd.comp (Computable.snd.comp Computable.fst)
      exact isREIn_of_computableIn_decide B _
        (computable₂_ratLt.computableIn₂.comp h3 h4.computableIn)
    have hiff : ∀ ib : ℕ × (ℕ × ℚ), P.ι ib.1 ∈ basicBall P ib.2 ↔
        ∃ n, qd ((ib.1, ib.2.1), n) + (2 : ℚ)⁻¹ ^ n < ib.2.2 := by
      intro ib
      constructor
      · intro h
        have h' : dist (P.ι ib.1) (P.ι ib.2.1) < ib.2.2 := Metric.mem_ball.mp h
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
          (show 0 < ((ib.2.2 : ℝ) - dist (P.ι ib.1) (P.ι ib.2.1)) / 2 by linarith)
          (by norm_num : (2 : ℝ)⁻¹ < 1)
        refine ⟨n, ?_⟩
        have herr := (abs_lt.mp (hqderr (ib.1, ib.2.1) n)).2
        have : ((qd ((ib.1, ib.2.1), n) + (2 : ℚ)⁻¹ ^ n : ℚ) : ℝ) < ib.2.2 := by
          push_cast
          linarith
        exact_mod_cast this
      · rintro ⟨n, hn⟩
        have hn' : ((qd ((ib.1, ib.2.1), n) + (2 : ℚ)⁻¹ ^ n : ℚ) : ℝ) < ib.2.2 := by
          exact_mod_cast hn
        push_cast at hn'
        have herr := (abs_lt.mp (hqderr (ib.1, ib.2.1) n)).1
        exact Metric.mem_ball.mpr (by linarith)
    obtain ⟨f, hf, hdom⟩ := hcert.exists
    exact ⟨f, hf, fun ib ↦ (hiff ib).trans (hdom ib)⟩
  -- the search predicate on witnesses `((i, k, m), b, c)`
  have hF : IsREIn B fun w : (ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ) ↦
      R (qk (w.1.2.1, w.1.2.2), w.2.1, w.2.2) ∧ P.ι w.1.1 ∈ basicBall P w.2.1 ∧
        w.2.2.2 < (2 : ℚ)⁻¹ ^ w.1.2.2 := by
    have hg1 : Computable fun w : (ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ) ↦
        (qk (w.1.2.1, w.1.2.2), w.2.1, w.2.2) :=
      (hqk.comp ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (Computable.snd.comp (Computable.snd.comp Computable.fst)))).pair
        ((Computable.fst.comp Computable.snd).pair (Computable.snd.comp Computable.snd))
    have hg2 : Computable fun w : (ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ) ↦ (w.1.1, w.2.1) :=
      (Computable.fst.comp Computable.fst).pair (Computable.fst.comp Computable.snd)
    have h3 : IsREIn B fun w : (ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ) ↦
        w.2.2.2 < (2 : ℚ)⁻¹ ^ w.1.2.2 :=
      isREIn_of_computable_decide (computable₂_ratLt.comp
        (Computable.snd.comp (Computable.snd.comp Computable.snd))
        (hpow.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))
    exact (IsREIn.comp (f := fun w : (ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ) ↦
        (qk (w.1.2.1, w.1.2.2), w.2.1, w.2.2)) hR hg1.computableIn).and
      ((IsREIn.comp (f := fun w : (ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ) ↦ (w.1.1, w.2.1)) hmem
        hg2.computableIn).and h3)
  obtain ⟨e, he, henum⟩ := (relative_enumeration B _).mp hF
  obtain ⟨step, hstep_def⟩ : ∃ step : (ℕ × ℕ × ℕ) × ℕ → Option ℕ, step = fun kt ↦
      (e kt.2).bind fun w ↦ if w.1 = kt.1 then some w.2.2.1 else none := ⟨_, rfl⟩
  have hstep : ComputableIn {charOracle B} step := by
    rw [hstep_def]
    have hg : Primrec fun p : ((ℕ × ℕ × ℕ) × Option ((ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ))) ×
        ((ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ)) ↦
        if p.2.1 = p.1.1 then some p.2.2.2.1 else none :=
      Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.option_some.comp (Primrec.fst.comp (Primrec.snd.comp
          (Primrec.snd.comp Primrec.snd)))) (Primrec.const none)
    have h0 : Computable fun q : (ℕ × ℕ × ℕ) × Option ((ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ)) ↦
        q.2.bind fun w ↦ if w.1 = q.1 then some w.2.2.1 else none :=
      Computable.option_bind
        (f := fun q : (ℕ × ℕ × ℕ) × Option ((ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ)) ↦ q.2)
        (g := fun (q : (ℕ × ℕ × ℕ) × Option ((ℕ × ℕ × ℕ) × (ℕ × ℚ) × (ℕ × ℚ))) w ↦
          if w.1 = q.1 then some w.2.2.1 else none) Computable.snd hg.to_comp
    exact (h0.computableIn.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd))).of_eq
      fun _ ↦ rfl
  obtain ⟨F, hF_def⟩ : ∃ F : ℕ × ℕ × ℕ × ℕ →. ℕ,
      F = fun d ↦ Nat.rfindOpt fun t ↦ step ((d.1, d.2.2.1, d.2.2.2), t) := ⟨_, rfl⟩
  have hFpr : PartrecIn {charOracle A} F := by
    rw [hF_def]
    refine partrecIn_mono A hBA (PartrecIn.rfindOpt (ComputableIn₂.mk ?_))
    have hk : Computable fun d : ℕ × ℕ × ℕ × ℕ ↦ (d.1, d.2.2.1, d.2.2.2) :=
      Computable.fst.pair ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd)))
    exact (hstep.comp ((hk.computableIn.comp ComputableIn.fst).pair ComputableIn.snd)).of_eq
      fun _ ↦ rfl
  obtain ⟨cF, hcF⟩ := oracleNatComplexity_le_of_decoder A F hFpr
  obtain ⟨c₁, hc₁⟩ := oracle_tuple_bounds_overhead A
  obtain ⟨c₂, hc₂⟩ := oracleNatComplexity_le_log_add_loglog A
  set cN : ℝ := Real.logb 2 (2 * N + 1) with hcN
  have hcN0 : 0 ≤ cN := Real.logb_nonneg one_lt_two (by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith)
  set K₀ : ℝ := (oracleNatComplexity A 0 : ℝ) + cF + c₁ + c₂ with hK₀
  /- The complexity chain at every precision `m`. -/
  have hchain : ∀ m : ℕ,
      (precisionComplexityNat P A x (Cfc * dyadicRadius m) : ℝ) ≤
        precisionComplexityNat P A z (dyadicRadius m) + m +
          (cN + 2 * Real.logb 2 (m + cN + 1) + 2 * Real.logb 2 ((m : ℝ) + 1) + K₀) := by
    intro m
    set δ : ℝ := dyadicRadius m with hδdef
    have hδ : 0 < δ := dyadicRadius_pos m
    have hδ1 : δ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hδ2 : δ * 2 ^ m = 1 := by
      rw [hδdef, dyadicRadius, inv_pow, inv_mul_cancel₀ (pow_pos two_pos m).ne']
    have h2m1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hδq : (((2 : ℚ)⁻¹ ^ m : ℚ) : ℝ) = δ := by rw [hδdef, dyadicRadius]; push_cast; rfl
    obtain ⟨i, hi, hKi⟩ := staticPointDimensions_attained P A z δ hδ
    have hKi' : precisionComplexityNat P A z δ = oracleNatComplexity A i := by
      simp [precisionComplexityNat, hKi]
    -- the dyadic time
    have hNt : 1 ≤ (N : ℝ) - t₀ := by
      have := (abs_le.mp ha).2
      linarith
    set k : ℕ := ⌊((N : ℝ) - t₀) / δ⌋₊ with hk
    have hk1 : (k : ℝ) ≤ ((N : ℝ) - t₀) / δ := Nat.floor_le (by positivity)
    have hk2 : ((N : ℝ) - t₀) / δ < k + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hδ] at hk2
    rw [le_div_iff₀ hδ] at hk1
    set q : ℝ := k * δ - N with hq
    have hq1 : |q + t₀| ≤ δ := by
      rw [abs_le]
      constructor <;> nlinarith
    have hq2 : |q| ≤ N := by
      have h1 := abs_le.mp ha
      have h2 := abs_le.mp hq1
      rw [abs_le]
      constructor <;> linarith
    have hqk_cast : ((qk (k, m) : ℚ) : ℝ) = q := by
      rw [hqk_def, hq]
      push_cast
      rw [hδdef, dyadicRadius]
    have hk_bound : (k : ℝ) + 1 ≤ (2 * N + 1) * 2 ^ m := by
      have h1 := (abs_le.mp ha).1
      have h2 : (k : ℝ) * δ * 2 ^ m ≤ ((N : ℝ) - t₀) * 2 ^ m :=
        mul_le_mul_of_nonneg_right hk1 (by positivity)
      rw [mul_assoc, hδ2, mul_one] at h2
      have h3 : ((N : ℝ) - t₀) * 2 ^ m ≤ 2 * N * 2 ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      linarith
    have hlogk : Real.logb 2 ((k : ℝ) + 1) ≤ m + cN := by
      calc Real.logb 2 ((k : ℝ) + 1) ≤ Real.logb 2 ((2 * N + 1) * 2 ^ m) :=
            Real.logb_le_logb_of_le one_lt_two (by positivity) hk_bound
        _ = cN + m := by
            rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
              Real.logb_self_eq_one one_lt_two, mul_one]
        _ = m + cN := add_comm _ _
    have hlogk0 : 0 ≤ Real.logb 2 ((k : ℝ) + 1) := Real.logb_nonneg one_lt_two (by linarith)
    -- the ideal point `φ q (ι i)` has a certified approximation: the decoder halts
    have hexists : ∃ t : ℕ, ∃ q' : ℕ, q' ∈ step ((i, k, m), t) := by
      obtain ⟨m', hm'⟩ := Metric.denseRange_iff.mp P.dense (G.φ q (P.ι i)) (δ / 2) (by positivity)
      obtain ⟨rc, hrc1, hrc2⟩ := exists_rat_btwn (half_lt_self hδ)
      have hc : G.φ q (P.ι i) ∈ basicBall P (m', rc) := Metric.mem_ball.mpr (hm'.trans hrc1)
      rw [← hqk_cast] at hc
      obtain ⟨b, hb, hib⟩ := hcomp (qk (k, m)) (P.ι i) (m', rc) hc
      have hrc2' : rc < (2 : ℚ)⁻¹ ^ m := by
        rw [← Rat.cast_lt (K := ℝ), hδq]
        exact hrc2
      obtain ⟨t, ht⟩ := (henum ((i, k, m), b, (m', rc))).mp ⟨hb, hib, hrc2'⟩
      refine ⟨t, m', ?_⟩
      rw [hstep_def]
      dsimp only
      simp [ht]
    have hdomF : (F (i, 0, k, m)).Dom := by
      rw [hF_def]
      dsimp only
      exact Nat.rfindOpt_dom.mpr hexists
    -- every output is within `Cfc δ` of `x`
    have hout : ∀ q' ∈ F (i, 0, k, m), dist (P.ι q') x < Cfc * δ := by
      intro q' hq'
      rw [hF_def] at hq'
      dsimp only at hq'
      obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hq'
      rw [hstep_def] at ht
      dsimp only at ht
      rw [Option.mem_def, Option.bind_eq_some_iff] at ht
      obtain ⟨w, hw, hqw⟩ := ht
      by_cases hkw : w.1 = (i, k, m)
      swap
      · simp [hkw] at hqw
      simp only [hkw, ite_true, Option.some_inj] at hqw
      subst hqw
      obtain ⟨hRw, hib, hrad⟩ := (henum w).mpr ⟨t, hw⟩
      rw [hkw] at hRw hib hrad
      dsimp only at hRw hib hrad
      have hmem' : G.φ ((qk (k, m) : ℚ) : ℝ) (P.ι i) ∈ basicBall P w.2.2 :=
        (hsound _ _ _ hRw).2.2 ⟨P.ι i, hib, rfl⟩
      rw [hqk_cast] at hmem'
      have hd1 : dist (G.φ q (P.ι i)) (P.ι w.2.2.1) < δ := by
        have h1 : dist (G.φ q (P.ι i)) (P.ι w.2.2.1) < (w.2.2.2 : ℝ) := Metric.mem_ball.mp hmem'
        have h2 : (w.2.2.2 : ℝ) < δ := by
          rw [← hδq]
          exact_mod_cast hrad
        exact h1.trans h2
      have hd2 : dist (G.φ q (P.ι i)) (G.φ q z) ≤ G.L ^ N * δ := by
        calc dist (G.φ q (P.ι i)) (G.φ q z) ≤ G.L ^ N * dist (P.ι i) z := hLip N q hq2 _ _
          _ ≤ G.L ^ N * δ := mul_le_mul_of_nonneg_left hi.le (by positivity)
      have hd3 : dist (G.φ q z) x ≤ G.V * δ := by
        have e : G.φ q z = G.φ (q + t₀) x := by
          rw [hz, ← Flow.map_add]
        rw [e]
        calc dist (G.φ (q + t₀) x) x ≤ G.V * |q + t₀| :=
              G.speed_unit (q + t₀) (hq1.trans hδ1) x
          _ ≤ G.V * δ := mul_le_mul_of_nonneg_left hq1 hV0
      calc dist (P.ι w.2.2.1) x
          ≤ dist (P.ι w.2.2.1) (G.φ q (P.ι i)) + dist (G.φ q (P.ι i)) (G.φ q z) +
            dist (G.φ q z) x := dist_triangle4 _ _ _ _
        _ < δ + G.L ^ N * δ + G.V * δ := by
            rw [dist_comm] at hd1
            linarith
        _ = Cfc * δ := by rw [hCfc]; ring
    -- the complexity bound
    set q' := (F (i, 0, k, m)).get hdomF with hq'
    have hq'mem : q' ∈ F (i, 0, k, m) := Part.get_mem hdomF
    have hKx : precisionComplexityNat P A x (Cfc * δ) ≤ oracleNatComplexity A q' :=
      precisionComplexityNat_le_of_dist_lt P A (hout q' hq'mem)
    have hKq := hcF i 0 k m q' hq'mem
    have hKpair := hc₁ k m
    have hKk := hc₂ k
    have hloglog : Real.logb 2 (Real.logb 2 ((k : ℝ) + 1) + 1) ≤
        Real.logb 2 ((m : ℝ) + cN + 1) :=
      Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
    have hKxR : (precisionComplexityNat P A x (Cfc * δ) : ℝ) ≤ oracleNatComplexity A q' := by
      exact_mod_cast hKx
    have hKqR : (oracleNatComplexity A q' : ℝ) ≤ oracleNatComplexity A i +
        oracleNatComplexity A 0 + oraclePairComplexity A k m + cF := by
      exact_mod_cast hKq
    rw [hKi']
    linarith
  /- The dimension bookkeeping. -/
  have hzero : Tendsto (fun m : ℕ ↦ dyadicRadius m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hratio_z : Tendsto (fun m : ℕ ↦ Real.log (dyadicRadius (m + 1)) / Real.log (dyadicRadius m))
      atTop (𝓝 1) := by
    have := tendsto_log_geometric_ratio (a := 1) (r := (2 : ℝ)⁻¹) one_pos (by norm_num)
      (by norm_num)
    refine this.congr fun m ↦ ?_
    simp [dyadicRadius]
  have hzero_x : Tendsto (fun m : ℕ ↦ Cfc * dyadicRadius m) atTop (𝓝 0) := by
    have := hzero.const_mul Cfc
    rwa [mul_zero] at this
  have hratio_x : Tendsto (fun m : ℕ ↦ Real.log (Cfc * dyadicRadius (m + 1)) /
      Real.log (Cfc * dyadicRadius m)) atTop (𝓝 1) :=
    tendsto_log_geometric_ratio hCfc0 (by norm_num) (by norm_num)
  have hdim_z2 := dimension_along_scales_upper P A z (fun m ↦ dyadicRadius m)
    (fun m ↦ dyadicRadius_pos m) hzero hratio_z
  have hdim_z1 := dimension_along_scales P A z (fun m ↦ dyadicRadius m)
    (fun m ↦ dyadicRadius_pos m) hzero hratio_z
  have hdim_x2 := dimension_along_scales_upper P A x (fun m ↦ Cfc * dyadicRadius m)
    (fun m ↦ mul_pos hCfc0 (dyadicRadius_pos m)) hzero_x hratio_x
  have hdim_x1 := dimension_along_scales P A x (fun m ↦ Cfc * dyadicRadius m)
    (fun m ↦ mul_pos hCfc0 (dyadicRadius_pos m)) hzero_x hratio_x
  -- the normalized quantities as real quotients
  have eKz : ∀ m : ℕ, 0 < m → normalizedPrecisionComplexity P A z (dyadicRadius m) =
      ENNReal.ofReal ((precisionComplexityNat P A z (dyadicRadius m) : ℝ) / m) := by
    intro m hm
    rw [normalizedPrecisionComplexity, neg_logb_dyadicRadius,
      ENNReal.ofReal_div_of_pos (by exact_mod_cast hm), ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  have eKx : ∀ m : ℕ, 0 < (m : ℝ) - cL →
      normalizedPrecisionComplexity P A x (Cfc * dyadicRadius m) =
        ENNReal.ofReal ((precisionComplexityNat P A x (Cfc * dyadicRadius m) : ℝ) / (m - cL)) := by
    intro m hm
    have hlog : -Real.logb 2 (Cfc * dyadicRadius m) = m - cL := by
      rw [Real.logb_mul hCfc0.ne' (dyadicRadius_pos m).ne']
      have := neg_logb_dyadicRadius m
      rw [hcL]
      linarith
    rw [normalizedPrecisionComplexity, hlog, ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_natCast]
  /- A sublinear bound on the logarithmic error. -/
  have hlog_lin : ∀ η' : ℝ, 0 < η' → ∃ c : ℝ, ∀ y : ℝ, 1 ≤ y → 2 * Real.logb 2 y ≤ η' * y + c := by
    intro η' hη'
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    set s : ℝ := η' * Real.log 2 / 2 with hs
    have hs0 : 0 < s := by positivity
    refine ⟨2 * (-1 - Real.log s) / Real.log 2, fun y hy ↦ ?_⟩
    have hy0 : 0 < y := by linarith
    have h1 : Real.log (s * y) ≤ s * y - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_mul hs0.ne' hy0.ne'] at h1
    have h2 : 2 * ((s * y - 1 - Real.log s) / Real.log 2) =
        η' * y + 2 * (-1 - Real.log s) / Real.log 2 := by
      rw [hs]
      field_simp
      ring
    calc 2 * Real.logb 2 y = 2 * (Real.log y / Real.log 2) := by rw [Real.logb]
      _ ≤ 2 * ((s * y - 1 - Real.log s) / Real.log 2) := by gcongr; linarith
      _ = _ := h2
  /- Claim: for every `η > 0`, both dimensions of `x` are bounded by `(1+η)` times those of
  `z` plus `(1+η)`. -/
  have claim : ∀ η : ℝ, 0 < η →
      (staticPointDimensions P A x).2 ≤
        ENNReal.ofReal (1 + η) * (staticPointDimensions P A z).2 + ENNReal.ofReal (1 + η) ∧
      (staticPointDimensions P A x).1 ≤
        ENNReal.ofReal (1 + η) * (staticPointDimensions P A z).1 + ENNReal.ofReal (1 + η) := by
    intro η hη
    obtain ⟨cη, hcη⟩ := hlog_lin (η / 4) (by positivity)
    -- the eventual real inequalities
    have hbig : ∀ᶠ m : ℕ in atTop,
        (2 * ((1 + η) * cL) / η : ℝ) ≤ m ∧
        (2 * (cN + K₀ + 2 * cη + (η / 4) * (cN + 2) + (1 + η) * cL) / η : ℝ) ≤ m ∧
        (1 : ℝ) ≤ m ∧ cL + 1 ≤ m := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * ((1 + η) * cL) / η),
        tendsto_natCast_atTop_atTop.eventually_ge_atTop
          (2 * (cN + K₀ + 2 * cη + (η / 4) * (cN + 2) + (1 + η) * cL) / η),
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ),
        tendsto_natCast_atTop_atTop.eventually_ge_atTop (cL + 1)] with m h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    have hev : ∀ᶠ m : ℕ in atTop,
        normalizedPrecisionComplexity P A x (Cfc * dyadicRadius m) ≤
          ((fun m : ℕ ↦ ENNReal.ofReal (1 + η) *
            normalizedPrecisionComplexity P A z (dyadicRadius m) : ℕ → ℝ≥0∞) +
            fun _ : ℕ ↦ ENNReal.ofReal (1 + η)) m := by
      filter_upwards [hbig] with m hm
      obtain ⟨hm1, hm4, hm2, hm3⟩ := hm
      have hm0 : (0 : ℝ) < m := by linarith
      have hmc : 0 < (m : ℝ) - cL := by linarith
      have hm0' : 0 < m := by exact_mod_cast hm0
      rw [Pi.add_apply]
      rw [eKx m hmc, eKz m hm0', ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      set u : ℝ := (precisionComplexityNat P A z (dyadicRadius m) : ℝ) with hu
      set v : ℝ := (precisionComplexityNat P A x (Cfc * dyadicRadius m) : ℝ) with hv
      have hu0 : 0 ≤ u := Nat.cast_nonneg _
      have hch := hchain m
      rw [← hu, ← hv] at hch
      have hl1 := hcη ((m : ℝ) + cN + 1) (by linarith)
      have hl2 := hcη ((m : ℝ) + 1) (by linarith)
      rw [div_le_iff₀ hη] at hm1 hm4
      have hηcL : 0 ≤ η * cL := by positivity
      -- `(1+η)(m - cL) ≥ m` and `(1+η)(m - cL) ≥ m + err`
      have hC : (m : ℝ) ≤ (1 + η) * (m - cL) := by linarith
      have hD : (m : ℝ) + (cN + 2 * Real.logb 2 (m + cN + 1) + 2 * Real.logb 2 ((m : ℝ) + 1) + K₀)
          ≤ (1 + η) * (m - cL) := by linarith
      have h₁ : u ≤ (1 + η) * (u / m) * (m - cL) := by
        have : u = u / m * m := (div_mul_cancel₀ u hm0.ne').symm
        calc u = u / m * m := this
          _ ≤ u / m * ((1 + η) * (m - cL)) :=
              mul_le_mul_of_nonneg_left hC (div_nonneg hu0 hm0.le)
          _ = (1 + η) * (u / m) * (m - cL) := by ring
      rw [div_le_iff₀ hmc]
      calc v ≤ u + (m + (cN + 2 * Real.logb 2 (m + cN + 1) +
            2 * Real.logb 2 ((m : ℝ) + 1) + K₀)) := by linarith
        _ ≤ (1 + η) * (u / m) * (m - cL) + (1 + η) * (m - cL) := add_le_add h₁ hD
        _ = ((1 + η) * (u / m) + (1 + η)) * (m - cL) := by ring
    constructor
    · rw [hdim_x2, hdim_z2]
      calc limsup (fun m ↦ normalizedPrecisionComplexity P A x (Cfc * dyadicRadius m)) atTop
          ≤ limsup ((fun m ↦ ENNReal.ofReal (1 + η) *
              normalizedPrecisionComplexity P A z (dyadicRadius m)) +
              fun _ ↦ ENNReal.ofReal (1 + η)) atTop := limsup_le_limsup hev
        _ ≤ limsup (fun m ↦ ENNReal.ofReal (1 + η) *
              normalizedPrecisionComplexity P A z (dyadicRadius m)) atTop +
            limsup (fun _ : ℕ ↦ ENNReal.ofReal (1 + η)) atTop := ennreal_limsup_add_le _ _
        _ = ENNReal.ofReal (1 + η) *
              limsup (fun m ↦ normalizedPrecisionComplexity P A z (dyadicRadius m)) atTop +
            ENNReal.ofReal (1 + η) := by
            rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, limsup_const]
    · rw [hdim_x1, hdim_z1]
      have hmono : Monotone fun t : ℝ≥0∞ ↦ ENNReal.ofReal (1 + η) * t + ENNReal.ofReal (1 + η) :=
        fun _ _ hab ↦ add_le_add (mul_le_mul' le_rfl hab) le_rfl
      have hcont : ContinuousAt (fun t : ℝ≥0∞ ↦ ENNReal.ofReal (1 + η) * t + ENNReal.ofReal (1 + η))
          (liminf (fun m ↦ normalizedPrecisionComplexity P A z (dyadicRadius m)) atTop) :=
        ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).add continuous_const).continuousAt
      calc liminf (fun m ↦ normalizedPrecisionComplexity P A x (Cfc * dyadicRadius m)) atTop
          ≤ liminf ((fun t : ℝ≥0∞ ↦ ENNReal.ofReal (1 + η) * t + ENNReal.ofReal (1 + η)) ∘
              fun m ↦ normalizedPrecisionComplexity P A z (dyadicRadius m)) atTop :=
            liminf_le_liminf hev
        _ = ENNReal.ofReal (1 + η) *
              liminf (fun m ↦ normalizedPrecisionComplexity P A z (dyadicRadius m)) atTop +
            ENNReal.ofReal (1 + η) :=
            (hmono.map_liminf_of_continuousAt _ hcont).symm
  /- Let `η → 0`. -/
  have h1 : Tendsto (fun η : ℝ ↦ ENNReal.ofReal (1 + η)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 : Tendsto (fun η : ℝ ↦ 1 + η) (𝓝 (0 : ℝ)) (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_id
    have := ENNReal.tendsto_ofReal h0
    rw [add_zero, ENNReal.ofReal_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : ∀ D : ℝ≥0∞, Tendsto (fun η : ℝ ↦ ENNReal.ofReal (1 + η) * D + ENNReal.ofReal (1 + η))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 + D)) := by
    intro D
    have := (ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero) (b := D)).add h1
    rwa [one_mul, add_comm] at this
  constructor
  · exact ge_of_tendsto (hlim _) (eventually_nhdsWithin_of_forall fun η hη ↦ (claim η hη).1)
  · exact ge_of_tendsto (hlim _) (eventually_nhdsWithin_of_forall fun η hη ↦ (claim η hη).2)

/-- Upper dimension (PO §4.2 step 5, packing side, with the flow coordinate restored): for
`x ∈ 𝓡` with positive rates,
`Dim^A(x) ≤ 1 + Dim^A_BS(x, f, u⁺) + Dim^A_BS(x, f⁻¹, u⁻)`.
Proof: for each admissible `(c, ρ)` the interface gives a shifted section point `z = φ t₀ x`;
`dimension_along_scales_upper` along `δ p`, the chain of `precision_chain`, the
multiplicative bookkeeping `S_{Tp} u⁺(x) / ((1-θ) p) ≤ (1+θ')/(1-θ) + o(1)`,
`limsup_comp_le_of_tendsto_atTop` for the two subsequences,
`centeredBSCost_timeLimit_le_pointwiseBSDimension` (Chapter A) for the denominators bound
`Dim^A(z)`; `flow_coordinate` (`Dim x ≤ 1 + Dim z`) is applied before the limits
`q → ∞`, `ρ → 0`, `c → 1`. Blueprint nodes `geo:section-point-upper`, `geo:flow-coordinate`. -/
theorem sectionPoint_upper {B : Set ℕ} (E : EffectiveGeodesicData G P B)
    (hBA : charOracle B ≤ᵀ charOracle A) (hA : OrbitToLocationEstimate G P A) {x : X}
    (hx : G.ControlledReturns x) (hpos : G.PositiveRates x) :
    (staticPointDimensions P A x).2 ≤
      1 + (pointwiseBSDimension P G.f G.uPlus A x).2 +
        (pointwiseBSDimension P G.finv G.uMinus A x).2 := by
  obtain ⟨lam, hlam, N₀, hmain⟩ := precision_chain_aux P hA hx hpos
  obtain ⟨-, hu0, huM⟩ := G.uPlus_props
  obtain ⟨-, hv0, hvM⟩ := G.uMinus_props
  replace huM : ∀ y, G.uPlus y ≤ G.Λ' := huM
  replace hvM : ∀ y, G.uMinus y ≤ G.Λ' := hvM
  have hΛ0 : 0 ≤ G.Λ' := (hu0 x).trans (huM x)
  obtain ⟨q₁, η₁, hη₁, hbs₁⟩ := centeredBSCost_timeLimit_le_pointwiseBSDimension P G.f
    G.continuous_f G.uPlus G.uPlus_props.1 A x hpos.1 .upper
  obtain ⟨q₂, η₂, hη₂, hbs₂⟩ := centeredBSCost_timeLimit_le_pointwiseBSDimension P G.finv
    G.continuous_finv G.uMinus G.uMinus_props.1 A x hpos.2 .upper
  obtain ⟨lam₀, hlam₀, N₁, hN₁⟩ := hpos.exists_linear
  set Dp := (pointwiseBSDimension P G.f G.uPlus A x).2 with hDp
  set Dm := (pointwiseBSDimension P G.finv G.uMinus A x).2 with hDm
  /- Claim A: the bound with the multiplicative losses, for fixed admissible parameters. -/
  have claimA : ∀ c : ℝ, 1 < c → ∀ ρ : ℚ, 0 < ρ → (ρ : ℝ) < lam / 2 →
      2 * (ρ : ℝ) * (c - 1) < lam → ∀ M : ℝ,
      (1 + 2 * ((ρ : ℝ) + G.Λ' * (c - 1)) / lam) / (1 - 2 * (ρ : ℝ) * (c - 1) / lam) < M →
      ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
        (staticPointDimensions P A x).2 ≤
          1 + ENNReal.ofReal M * ((1 + η₁ q) * Dp + (1 + η₂ q) * Dm) := by
    intro c hc ρ hρ hρlam hθ M hM
    set θ : ℝ := 2 * (ρ : ℝ) * (c - 1) / lam with hθdef
    set θ' : ℝ := 2 * ((ρ : ℝ) + G.Λ' * (c - 1)) / lam with hθ'def
    obtain ⟨t₀, ht₀, ε, hε, Tp, Tm, δ, c₀, p₀, hδpos, hδ0, hratio, -, hlogδ, hTp, hTm, hbound,
      hSp, hSm, hchain⟩ := hmain c hc ρ hρ hρlam hθ
    set z := G.φ t₀ x with hz
    have hzx : (staticPointDimensions P A x).2 ≤ 1 + (staticPointDimensions P A z).2 :=
      (E.flow_coordinate P hBA ht₀).1
    rw [← hθdef] at hlogδ
    rw [← hθ'def] at hSp hSm
    obtain ⟨q₀, hq₀⟩ := exists_dyadicRadius_lt hε
    refine ⟨max q₀ (max q₁ q₂), fun q hq ↦ ?_⟩
    have hqε : dyadicRadius q ≤ ε :=
      (dyadicRadius_antitone (le_of_max_le_left hq)).trans hq₀.le
    have hq₁ : q₁ ≤ q := le_of_max_le_left (le_of_max_le_right hq)
    have hq₂ : q₂ ≤ q := le_of_max_le_right (le_of_max_le_right hq)
    have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ
    have hc1 : 0 ≤ c - 1 := by linarith
    have hθ1 : 0 < 1 - θ := by rw [hθdef, sub_pos, div_lt_one hlam]; exact hθ
    have hθ'0 : 0 ≤ θ' := by rw [hθ'def]; positivity
    have hM1 : 1 + θ' < M * (1 - θ) := by rwa [div_lt_iff₀ hθ1] at hM
    have hM0 : 0 < M := lt_trans (div_pos (by linarith) hθ1) hM
    have hMslope : 0 < M * (1 - θ) - (1 + θ') := by linarith
    -- eventual facts along `p`
    have hd₀ : Tendsto (fun p : ℕ ↦ (1 - θ) * p - c₀) atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c₀)
        (tendsto_natCast_atTop_atTop.const_mul_atTop hθ1)
    have hMd : Tendsto (fun p : ℕ ↦ (M * (1 - θ) - (1 + θ')) * p) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hMslope
    have hev : ∀ᶠ p : ℕ in atTop, p₀ ≤ p ∧ 0 < (1 - θ) * p - c₀ ∧
        c₀ + G.Λ' + M * c₀ ≤ (M * (1 - θ) - (1 + θ')) * p ∧
        N₁ ≤ Tp p + 1 ∧ N₁ ≤ Tm p + 1 := by
      filter_upwards [eventually_ge_atTop p₀, hd₀.eventually_gt_atTop 0,
        hMd.eventually_ge_atTop _, hTp.eventually_ge_atTop N₁, hTm.eventually_ge_atTop N₁]
        with p h1 h2 h3 h4 h5
      exact ⟨h1, h2, h3, h4.trans (Nat.le_succ _), h5.trans (Nat.le_succ _)⟩
    -- the pointwise bound
    have hpt : ∀ᶠ p : ℕ in atTop, normalizedPrecisionComplexity P A z (δ p) ≤
        ENNReal.ofReal M * centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q) +
        ENNReal.ofReal M * centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q) +
        ENNReal.ofReal ((2 * Real.logb 2 ((Tp p : ℝ) + 1) + 2 * Real.logb 2 ((Tm p : ℝ) + 1) +
          |c₀|) / ((1 - θ) * p - c₀)) := by
      filter_upwards [hev] with p hp
      obtain ⟨hp₀, hd, hMd', hNp, hNm⟩ := hp
      have hdd₀ : (1 - θ) * p - c₀ ≤ -Real.logb 2 (δ p) := hlogδ p
      have hd' : 0 < -Real.logb 2 (δ p) := hd.trans_le hdd₀
      have hSppos : 0 < birkhoffSum G.f G.uPlus (Tp p + 1) x :=
        lt_of_lt_of_le (mul_pos hlam₀ (Nat.cast_pos.2 (Nat.succ_pos _))) (hN₁ _ hNp).1
      have hSmpos : 0 < birkhoffSum G.finv G.uMinus (Tm p + 1) x :=
        lt_of_lt_of_le (mul_pos hlam₀ (Nat.cast_pos.2 (Nat.succ_pos _))) (hN₁ _ hNm).2
      have hSple : birkhoffSum G.f G.uPlus (Tp p + 1) x ≤ M * ((1 - θ) * p - c₀) := by
        have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := G.f) hu0 huM x
          (show Tp p ≤ Tp p + 1 by omega)).2
        simp only [add_tsub_cancel_left, Nat.cast_one, mul_one] at h1
        have h2 := hSp p
        linarith
      have hSmle : birkhoffSum G.finv G.uMinus (Tm p + 1) x ≤ M * ((1 - θ) * p - c₀) := by
        have h1 := (GeodesicReconstructionData.birkhoffSum_bounds_of_le (T := G.finv) hv0 hvM x
          (show Tm p ≤ Tm p + 1 by omega)).2
        simp only [add_tsub_cancel_left, Nat.cast_one, mul_one] at h1
        have h2 := hSm p
        linarith
      have hKR : (precisionComplexityNat P A z (δ p) : ℝ) ≤
          (orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q) : ℝ) +
          orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q) +
          (2 * Real.logb 2 ((Tp p : ℝ) + 1) + 2 * Real.logb 2 ((Tm p : ℝ) + 1) + |c₀|) := by
        have h1 := hchain p hp₀
        have h2 : (orbitComplexityNat P G.f A x (Tp p + 1) ε : ℝ) ≤
            orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q) := by
          exact_mod_cast orbitComplexityNat_anti_radius P G.f A x G.continuous_f (Tp p + 1)
            (dyadicRadius_pos q) hqε
        have h3 : (orbitComplexityNat P G.finv A x (Tm p + 1) ε : ℝ) ≤
            orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q) := by
          exact_mod_cast orbitComplexityNat_anti_radius P G.finv A x G.continuous_finv (Tm p + 1)
            (dyadicRadius_pos q) hqε
        linarith [le_abs_self c₀]
      -- the real inequality
      have hreal : (precisionComplexityNat P A z (δ p) : ℝ) / (-Real.logb 2 (δ p)) ≤
          M * ((orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q) : ℝ) /
              birkhoffSum G.f G.uPlus (Tp p + 1) x) +
            M * ((orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q) : ℝ) /
              birkhoffSum G.finv G.uMinus (Tm p + 1) x) +
            (2 * Real.logb 2 ((Tp p : ℝ) + 1) + 2 * Real.logb 2 ((Tm p : ℝ) + 1) + |c₀|) /
              ((1 - θ) * p - c₀) := by
        have h1 : (precisionComplexityNat P A z (δ p) : ℝ) / (-Real.logb 2 (δ p)) ≤
            precisionComplexityNat P A z (δ p) / ((1 - θ) * p - c₀) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hdd₀
        have h2 := div_le_div_of_nonneg_right hKR hd.le
        have h4 : (orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q) : ℝ) /
            birkhoffSum G.f G.uPlus (Tp p + 1) x * (birkhoffSum G.f G.uPlus (Tp p + 1) x /
              ((1 - θ) * p - c₀)) =
            orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q) / ((1 - θ) * p - c₀) := by
          rw [div_mul_div_comm, mul_comm (birkhoffSum G.f G.uPlus (Tp p + 1) x) ((1 - θ) * p - c₀),
            mul_div_mul_right _ _ hSppos.ne']
        have h5 : (orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q) : ℝ) /
            birkhoffSum G.finv G.uMinus (Tm p + 1) x * (birkhoffSum G.finv G.uMinus (Tm p + 1) x /
              ((1 - θ) * p - c₀)) =
            orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q) / ((1 - θ) * p - c₀) := by
          rw [div_mul_div_comm,
            mul_comm (birkhoffSum G.finv G.uMinus (Tm p + 1) x) ((1 - θ) * p - c₀),
            mul_div_mul_right _ _ hSmpos.ne']
        have h6 : birkhoffSum G.f G.uPlus (Tp p + 1) x / ((1 - θ) * p - c₀) ≤ M := by
          rw [div_le_iff₀ hd]; exact hSple
        have h7 : birkhoffSum G.finv G.uMinus (Tm p + 1) x / ((1 - θ) * p - c₀) ≤ M := by
          rw [div_le_iff₀ hd]; exact hSmle
        have h8 := mul_le_mul_of_nonneg_left h6 (div_nonneg
          (Nat.cast_nonneg (orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q))) hSppos.le)
        have h9 := mul_le_mul_of_nonneg_left h7 (div_nonneg
          (Nat.cast_nonneg (orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q)))
          hSmpos.le)
        rw [h4] at h8
        rw [h5] at h9
        rw [add_div, add_div] at h2
        rw [mul_comm M, mul_comm M]
        linarith
      -- back to `ℝ≥0∞`
      have eK : normalizedPrecisionComplexity P A z (δ p) =
          ENNReal.ofReal ((precisionComplexityNat P A z (δ p) : ℝ) / (-Real.logb 2 (δ p))) := by
        rw [normalizedPrecisionComplexity, ENNReal.ofReal_div_of_pos hd', ENNReal.ofReal_natCast]
      have eP : centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q) =
          ENNReal.ofReal ((orbitComplexityNat P G.f A x (Tp p + 1) (dyadicRadius q) : ℝ) /
            birkhoffSum G.f G.uPlus (Tp p + 1) x) := by
        rw [centeredBSCost, ENNReal.ofReal_div_of_pos hSppos, ENNReal.ofReal_natCast]
      have eM : centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q) =
          ENNReal.ofReal ((orbitComplexityNat P G.finv A x (Tm p + 1) (dyadicRadius q) : ℝ) /
            birkhoffSum G.finv G.uMinus (Tm p + 1) x) := by
        rw [centeredBSCost, ENNReal.ofReal_div_of_pos hSmpos, ENNReal.ofReal_natCast]
      rw [eK, eP, eM, ← ENNReal.ofReal_mul hM0.le, ← ENNReal.ofReal_mul hM0.le]
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      refine ENNReal.ofReal_add_le.trans ?_
      exact add_le_add ENNReal.ofReal_add_le le_rfl
    -- the error term tends to zero
    have he : Tendsto (fun p : ℕ ↦ ENNReal.ofReal ((2 * Real.logb 2 ((Tp p : ℝ) + 1) +
        2 * Real.logb 2 ((Tm p : ℝ) + 1) + |c₀|) / ((1 - θ) * p - c₀))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.tendsto_ofReal
      set α : ℝ := c * (2 / lam) with hα
      set β : ℝ := c * (N₀ + 1) + 1 with hβ
      have hα0 : 0 < α := by rw [hα]; positivity
      have hβ0 : 0 < β := by rw [hβ]; positivity
      have hy : Tendsto (fun p : ℕ ↦ α * p + β) atTop atTop :=
        tendsto_atTop_add_const_right atTop β (tendsto_natCast_atTop_atTop.const_mul_atTop hα0)
      have hTpβ : ∀ p : ℕ, (Tp p : ℝ) + 1 ≤ α * p + β := by
        intro p
        have := (hbound p).1
        have e : c * (2 * p / lam + N₀ + 1) = α * p + (β - 1) := by rw [hα, hβ]; ring
        linarith
      have hTmβ : ∀ p : ℕ, (Tm p : ℝ) + 1 ≤ α * p + β := by
        intro p
        have := (hbound p).2
        have e : c * (2 * p / lam + N₀ + 1) = α * p + (β - 1) := by rw [hα, hβ]; ring
        linarith
      -- `log (α p + β) / ((1 - θ) p - c₀) → 0`
      have hlog0 : Tendsto (fun p : ℕ ↦ Real.log (α * p + β) / ((1 - θ) * p - c₀)) atTop
          (𝓝 0) := by
        have hden : ∀ p : ℕ, (1 - θ) / α * (α * p + β) + (-c₀ - (1 - θ) / α * β) =
            (1 - θ) * p - c₀ := by
          intro p
          field_simp
          ring
        have h1 := (Real.tendsto_pow_log_div_mul_add_atTop ((1 - θ) / α) (-c₀ - (1 - θ) / α * β) 1
          (div_pos hθ1 hα0).ne').comp hy
        refine h1.congr fun p ↦ ?_
        simp only [Function.comp, pow_one, hden]
      have hlogb0 : Tendsto (fun p : ℕ ↦ Real.logb 2 (α * p + β) / ((1 - θ) * p - c₀)) atTop
          (𝓝 0) := by
        have := hlog0.div_const (Real.log 2)
        rw [zero_div] at this
        refine this.congr fun p ↦ ?_
        rw [Real.logb, div_right_comm]
      have hconst : Tendsto (fun p : ℕ ↦ |c₀| / ((1 - θ) * p - c₀)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hd₀
      have hupper : Tendsto (fun p : ℕ ↦ (4 * Real.logb 2 (α * p + β) + |c₀|) /
          ((1 - θ) * p - c₀)) atTop (𝓝 0) := by
        have := (hlogb0.const_mul 4).add hconst
        rw [mul_zero, add_zero] at this
        refine this.congr fun p ↦ ?_
        rw [add_div, mul_div_assoc]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hupper ?_ ?_
      · filter_upwards [hd₀.eventually_gt_atTop 0] with p hd
        apply div_le_div_of_nonneg_right _ hd.le
        have h1 : 0 ≤ Real.logb 2 ((Tp p : ℝ) + 1) :=
          Real.logb_nonneg one_lt_two (by linarith [(Nat.cast_nonneg (Tp p) : (0 : ℝ) ≤ Tp p)])
        have h2 : 0 ≤ Real.logb 2 ((Tm p : ℝ) + 1) :=
          Real.logb_nonneg one_lt_two (by linarith [(Nat.cast_nonneg (Tm p) : (0 : ℝ) ≤ Tm p)])
        linarith
      · filter_upwards [hd₀.eventually_gt_atTop 0] with p hd
        apply div_le_div_of_nonneg_right _ hd.le
        have h1 : Real.logb 2 ((Tp p : ℝ) + 1) ≤ Real.logb 2 (α * p + β) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) (hTpβ p)
        have h2 : Real.logb 2 ((Tm p : ℝ) + 1) ≤ Real.logb 2 (α * p + β) :=
          Real.logb_le_logb_of_le one_lt_two (by positivity) (hTmβ p)
        linarith
    -- the two subsequence limsups
    have hlimp : limsup (fun p ↦ centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q))
        atTop ≤ (1 + η₁ q) * Dp := by
      refine le_trans (limsup_comp_le_of_tendsto_atTop
        (u := fun n ↦ centeredBSCost P G.f G.uPlus A x n (dyadicRadius q))
        ((tendsto_add_atTop_nat 1).comp hTp)) ?_
      exact hbs₁ q hq₁
    have hlimm : limsup (fun p ↦ centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q))
        atTop ≤ (1 + η₂ q) * Dm := by
      refine le_trans (limsup_comp_le_of_tendsto_atTop
        (u := fun n ↦ centeredBSCost P G.finv G.uMinus A x n (dyadicRadius q))
        ((tendsto_add_atTop_nat 1).comp hTm)) ?_
      exact hbs₂ q hq₂
    -- assemble
    refine hzx.trans (add_le_add le_rfl ?_)
    rw [dimension_along_scales_upper P A z δ hδpos hδ0 hratio]
    calc limsup (fun p ↦ normalizedPrecisionComplexity P A z (δ p)) atTop
        ≤ limsup ((fun p ↦ ENNReal.ofReal M *
            centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q) +
            ENNReal.ofReal M * centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q)) +
            fun p ↦ ENNReal.ofReal ((2 * Real.logb 2 ((Tp p : ℝ) + 1) +
              2 * Real.logb 2 ((Tm p : ℝ) + 1) + |c₀|) / ((1 - θ) * p - c₀))) atTop :=
          limsup_le_limsup hpt
      _ = limsup ((fun p ↦ ENNReal.ofReal M *
            centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q)) +
            fun p ↦ ENNReal.ofReal M *
              centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q)) atTop :=
          ENNReal.limsup_add_of_right_tendsto_zero he _
      _ ≤ limsup (fun p ↦ ENNReal.ofReal M *
            centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q)) atTop +
          limsup (fun p ↦ ENNReal.ofReal M *
            centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q)) atTop :=
          ennreal_limsup_add_le _ _
      _ = ENNReal.ofReal M *
            limsup (fun p ↦ centeredBSCost P G.f G.uPlus A x (Tp p + 1) (dyadicRadius q)) atTop +
          ENNReal.ofReal M *
            limsup (fun p ↦ centeredBSCost P G.finv G.uMinus A x (Tm p + 1) (dyadicRadius q))
              atTop := by
          rw [ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal M * ((1 + η₁ q) * Dp) + ENNReal.ofReal M * ((1 + η₂ q) * Dm) := by
          gcongr
      _ = ENNReal.ofReal M * ((1 + η₁ q) * Dp + (1 + η₂ q) * Dm) := by rw [mul_add]
  /- Claim B: the bound with a single multiplicative loss `κ > 1`. -/
  have claimB : ∀ κ : ℝ, 1 < κ → (staticPointDimensions P A x).2 ≤
      1 + ENNReal.ofReal κ * (Dp + Dm) := by
    intro κ hκ
    set r : ℝ := Real.sqrt κ with hr
    have hr1 : 1 < r := by
      rw [hr, Real.lt_sqrt zero_le_one]
      linarith
    have hr0 : 0 < r := by linarith
    have hrr : r * r = κ := Real.mul_self_sqrt (by linarith)
    -- the admissible parameters
    set t₀ : ℝ := min 1 (min (lam / 4) ((r - 1) * lam / (2 * (1 + G.Λ' + r)))) with ht₀
    have ht₀pos : 0 < t₀ := by
      rw [ht₀]
      refine lt_min one_pos (lt_min (by positivity) (div_pos (mul_pos (by linarith) hlam)
        (by positivity)))
    obtain ⟨ρ, hρ0, hρt⟩ := exists_rat_btwn ht₀pos
    have hρ' : (0 : ℝ) < ρ := by exact_mod_cast hρ0
    have hρ0' : (0 : ℚ) < ρ := by exact_mod_cast hρ0
    have hρ1 : (ρ : ℝ) ≤ 1 := (hρt.le.trans (min_le_left _ _))
    have hρ4 : (ρ : ℝ) < lam / 4 := hρt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hρr : (ρ : ℝ) < (r - 1) * lam / (2 * (1 + G.Λ' + r)) :=
      hρt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hρρ : (ρ : ℝ) * ρ ≤ ρ := by nlinarith
    have hA1 : 2 * (ρ : ℝ) * (1 + G.Λ' + r) < (r - 1) * lam := by
      rw [lt_div_iff₀ (by positivity)] at hρr
      linarith
    have hc : 1 < 1 + (ρ : ℝ) := by linarith
    have hc1 : (1 + (ρ : ℝ)) - 1 = ρ := add_sub_cancel_left 1 (ρ : ℝ)
    have hρlam : (ρ : ℝ) < lam / 2 := by linarith
    have hθ : 2 * (ρ : ℝ) * ((1 + (ρ : ℝ)) - 1) < lam := by rw [hc1]; nlinarith
    have hθ1 : 0 < 1 - 2 * (ρ : ℝ) * ((1 + (ρ : ℝ)) - 1) / lam := by
      rw [sub_pos, div_lt_one hlam]; exact hθ
    have hM : (1 + 2 * ((ρ : ℝ) + G.Λ' * ((1 + (ρ : ℝ)) - 1)) / lam) /
        (1 - 2 * (ρ : ℝ) * ((1 + (ρ : ℝ)) - 1) / lam) < r := by
      rw [div_lt_iff₀ hθ1, hc1]
      have e : r * (1 - 2 * (ρ : ℝ) * ρ / lam) - (1 + 2 * ((ρ : ℝ) + G.Λ' * ρ) / lam) =
          (r * lam - 2 * r * (ρ * ρ) - lam - 2 * ρ - 2 * G.Λ' * ρ) / lam := by
        field_simp
        ring
      have h1 : r * (ρ * ρ) ≤ r * ρ := mul_le_mul_of_nonneg_left hρρ hr0.le
      have : 0 < r * (1 - 2 * (ρ : ℝ) * ρ / lam) - (1 + 2 * ((ρ : ℝ) + G.Λ' * ρ) / lam) := by
        rw [e]
        apply div_pos _ hlam
        linarith
      linarith
    obtain ⟨q₀, hq₀⟩ := claimA (1 + ρ) hc ρ hρ0' hρlam hθ r hM
    -- choose the dyadic precision
    have hη₁' := (ENNReal.tendsto_nhds_zero.1 hη₁) (ENNReal.ofReal (r - 1))
      (ENNReal.ofReal_pos.2 (by linarith))
    have hη₂' := (ENNReal.tendsto_nhds_zero.1 hη₂) (ENNReal.ofReal (r - 1))
      (ENNReal.ofReal_pos.2 (by linarith))
    obtain ⟨q, hq, hq1, hq2⟩ := (eventually_ge_atTop q₀).and (hη₁'.and hη₂') |>.exists
    have e1 : (1 : ℝ≥0∞) + ENNReal.ofReal (r - 1) = ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
      congr 1
      ring
    have h1 : 1 + η₁ q ≤ ENNReal.ofReal r := by rw [← e1]; exact add_le_add le_rfl hq1
    have h2 : 1 + η₂ q ≤ ENNReal.ofReal r := by rw [← e1]; exact add_le_add le_rfl hq2
    calc (staticPointDimensions P A x).2
        ≤ 1 + ENNReal.ofReal r * ((1 + η₁ q) * Dp + (1 + η₂ q) * Dm) := hq₀ q hq
      _ ≤ 1 + ENNReal.ofReal r * (ENNReal.ofReal r * Dp + ENNReal.ofReal r * Dm) := by gcongr
      _ = 1 + ENNReal.ofReal (r * r) * (Dp + Dm) := by
          rw [ENNReal.ofReal_mul hr0.le]
          ring
      _ = 1 + ENNReal.ofReal κ * (Dp + Dm) := by rw [hrr]
  /- Claim C: let `κ → 1`. -/
  rw [add_assoc]
  by_cases htop : Dp + Dm = ⊤
  · rw [htop, add_top]; exact le_top
  · have h1 : Tendsto (fun κ : ℝ ↦ ENNReal.ofReal κ) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (1 : ℝ)))
      rw [ENNReal.ofReal_one] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun κ : ℝ ↦ 1 + ENNReal.ofReal κ * (Dp + Dm)) (𝓝[>] (1 : ℝ))
        (𝓝 (1 + (Dp + Dm))) := by
      have := ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero) (b := Dp + Dm)
      rw [one_mul] at this
      exact tendsto_const_nhds.add this
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun κ hκ ↦ claimB κ hκ)

end limits

end Kolmogorov.PointToSet
