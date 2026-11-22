/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness

/-!
# Orbit complexity on a shift versus the complexity of prefixes

On a one-sided shift with a first-difference metric `d(x, y) = β^{firstDiff x y}` the Bowen ball
`B_n(x, σ, β^k)` is the cylinder `[x↾(n+k)]` (`bowenBall_shiftMap_eq_cylinder`). If the symbols of
the ideal points of the presentation are `A`-computable (`hP`), then:

* `orbitComplexities_snd_le_limsup_wordComplexity`: from a word `w` one finds, by an `A`-computable
  search, an index `i` with `x_i ∈ [w]` (decidable from `hP` by comparing the first `|w|`
  symbols); on `w = x↾(n+k)` the search halts, since the Bowen ball `[x↾(n+k)]` contains an ideal
  point (`bowen_ball_dense`). So `K_n^A(x, σ, β^k) ≤ K^A(x↾(n+k)) + c`, and
  `K̄^A(x, σ) ≤ limsup_n K^A(x↾n)/n`: at a dyadic scale `r ≥ β^k` use antitonicity in the radius,
  the constant `c / n` vanishes and the index shift `n ↦ n + k` does not change the upper rate;
* `liminf_wordComplexity_le_orbitComplexities_fst`: from the index `i` of an ideal point in
  `[x↾m]` and `m` one computes `x↾m = x_i↾m`, so `K^A(x↾m) ≤ K^A(i) + K^A(m) + c`. At the scale
  `1 = β^0 = dyadicRadius 0` the Bowen ball `B_n(x, σ, 1)` is `[x↾n]`, hence
  `K^A(x↾n)/n ≤ K_n^A(x, σ, 1)/n + (K^A(n) + c)/n`; since `K^A(n) = O(log n)`
  (`oracleNatComplexity_le_log_add_loglog`) the last term tends to `0`, and
  `liminf_n K^A(x↾n)/n ≤ K̲^A(x, σ)`.

Both statements hold for an arbitrary `β ∈ (0, 1)`, computable or not: every decision made by the
codes is a comparison of symbols. Blueprint node `erg:prop710`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

/-! ### Prefixes and cylinders -/

section prefixes

variable {α : Type*}

/-- The prefix of length `m + 1` is the prefix of length `m` followed by the symbol at `m`. -/
private lemma shiftTranslation_wordPrefix_succ (y : ℕ → α) (m : ℕ) :
    wordPrefix y (m + 1) = wordPrefix y m ++ [y m] := by
  rw [wordPrefix, List.ofFn_succ_last]
  rfl

/-- `y ∈ [x↾m]` iff the prefixes of length `m` of `y` and `x` coincide. -/
theorem shiftTranslation_mem_cylinder_iff {y x : ℕ → α} {m : ℕ} :
    y ∈ PiNat.cylinder x m ↔ wordPrefix y m = wordPrefix x m := by
  rw [PiNat.mem_cylinder_iff, wordPrefix, wordPrefix, List.ofFn_inj, funext_iff]
  exact ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩

/-- The prefix `y↾m` has length `m`. -/
private lemma shiftTranslation_length_wordPrefix (y : ℕ → α) (m : ℕ) :
    (wordPrefix y m).length = m :=
  List.length_ofFn

end prefixes

/-! ### Computability of prefixes of ideal points -/

section computable

variable {α : Type*} [Primcodable α]

/-- If the symbols `(i, j) ↦ f i j` are `A`-computable, so are the prefixes
`(i, m) ↦ (f i)↾m`. -/
theorem shiftTranslation_computableIn_wordPrefix {A : Set ℕ} {f : ℕ → ℕ → α}
    (hf : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ f q.1 q.2) :
    ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ wordPrefix (f q.1) q.2 := by
  have hh : ComputableIn₂ {charOracle A}
      fun (q : ℕ × ℕ) (p : ℕ × List α) ↦ p.2 ++ [f q.1 p.1] := by
    refine ComputableIn₂.mk ?_
    refine ((Computable.list_concat : Computable₂ fun (l : List α) (a : α) ↦ l ++ [a]).computableIn₂
      ).comp (Computable.snd.comp Computable.snd).computableIn
      (hf.comp (g := fun p : (ℕ × ℕ) × (ℕ × List α) ↦ (p.1.1, p.2.1)) ?_)
    exact ((Computable.fst.comp Computable.fst).pair
      (Computable.fst.comp Computable.snd)).computableIn
  refine (ComputableIn.nat_rec (f := fun q : ℕ × ℕ ↦ q.2) (g := fun _ ↦ ([] : List α))
    Computable.snd.computableIn (Computable.const []).computableIn hh).of_eq ?_
  rintro ⟨i, m⟩
  dsimp only
  induction m with
  | zero => rfl
  | succ m ih => rw [shiftTranslation_wordPrefix_succ, ← ih]

end computable

/-! ### Complexity bounds -/

/-- `(K^A(m) + c) / m → 0`: the complexity of a natural number is logarithmic. -/
private theorem shiftTranslation_tendsto_natComplexity_div (A : Set ℕ) (c : ℕ) :
    Tendsto (fun m : ℕ ↦ ((oracleNatComplexity A m + c : ℕ) : ℝ≥0∞) / m) atTop (𝓝 0) := by
  obtain ⟨c₀, hc₀⟩ := oracleNatComplexity_le_log_add_loglog A
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set C₁ : ℝ := (1 + 2 / Real.log 2) / Real.log 2 with hC₁
  set C₂ : ℝ := |c₀| + c with hC₂
  let u : ℕ → ℝ := fun m ↦ C₁ * (Real.log ((m : ℝ) + 1) / m) + C₂ / m
  have hlog : Tendsto (fun m : ℕ ↦ Real.log ((m : ℝ) + 1) / m) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    refine h.congr fun m ↦ ?_
    simp
  have hu : Tendsto u atTop (𝓝 0) := by
    have h := (hlog.const_mul C₁).add (tendsto_const_div_atTop_nhds_zero_nat C₂)
    simpa using h
  have hbound : ∀ m : ℕ, 1 ≤ m →
      ((oracleNatComplexity A m + c : ℕ) : ℝ≥0∞) / m ≤ ENNReal.ofReal (u m) := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_div_of_pos hm0]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [u]
    rw [mul_div_assoc', ← add_div, div_le_div_iff_of_pos_right hm0]
    have hK := hc₀ m
    set L : ℝ := Real.logb 2 ((m : ℝ) + 1) with hL
    have hL0 : 0 ≤ L := Real.logb_nonneg one_lt_two (by linarith)
    have hLL : Real.logb 2 (L + 1) ≤ L / Real.log 2 := by
      rw [Real.logb, div_le_div_iff_of_pos_right hl2]
      have := Real.log_le_sub_one_of_pos (show 0 < L + 1 by linarith)
      linarith
    have hLeq : L = Real.log ((m : ℝ) + 1) / Real.log 2 := rfl
    have hC : C₁ * Real.log ((m : ℝ) + 1) = L + 2 * (L / Real.log 2) := by
      rw [hC₁, hLeq]
      field_simp
    have hc0 : c₀ ≤ |c₀| := le_abs_self c₀
    push_cast
    rw [hC, hC₂]
    linarith
  have hupper : Tendsto (fun m ↦ ENNReal.ofReal (u m)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall fun _ ↦ bot_le) ((eventually_ge_atTop 1).mono hbound)

/-- `c / n → 0` in `ℝ≥0∞`. -/
private theorem shiftTranslation_tendsto_const_div (c : ℕ) :
    Tendsto (fun n : ℕ ↦ (c : ℝ≥0∞) / n) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
    (Or.inr (ENNReal.natCast_ne_top c))
  simpa [div_eq_mul_inv] using h

/-- Shifting the index by `k` while keeping the denominator `n` does not change the upper growth
rate (the upper half of the private `rate_add` of `Shift`). -/
private lemma shiftTranslation_limsup_add (a : ℕ → ℝ≥0∞) (k : ℕ) :
    limsup (fun n : ℕ ↦ a (n + k) / n) atTop = limsup (fun n : ℕ ↦ a n / n) atTop := by
  have hu := limsup_nat_add (fun n : ℕ ↦ a n / n) k
  rw [← hu]
  set v : ℕ → ℝ≥0∞ := fun n ↦ a (n + k) / ((n + k : ℕ) : ℝ≥0∞) with hv
  set w : ℕ → ℝ≥0∞ := fun n ↦ a (n + k) / (n : ℝ≥0∞) with hw
  have hvw : ∀ n, v n ≤ w n := fun n ↦
    ENNReal.div_le_div_left (by exact_mod_cast Nat.le_add_right n k) _
  have hwv : ∀ m : ℕ, 1 ≤ m → ∀ᶠ n in atTop, w n ≤ (1 + (m : ℝ≥0∞)⁻¹) * v n := by
    intro m hm
    filter_upwards [eventually_ge_atTop (k * m + 1)] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_pos _).trans_le hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hnk : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by push_cast; positivity
    have hinv : (n : ℝ≥0∞)⁻¹ ≤ (1 + (m : ℝ≥0∞)⁻¹) * ((n + k : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_natCast m,
        ← ENNReal.ofReal_natCast (n + k), ← ENNReal.ofReal_inv_of_pos hn0,
        ← ENNReal.ofReal_inv_of_pos hm0, ← ENNReal.ofReal_inv_of_pos hnk,
        ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hkm : (k : ℝ) * m ≤ n := by exact_mod_cast (Nat.le_succ _).trans hn
      push_cast
      rw [← sub_nonneg]
      have hnk' : (0 : ℝ) < n + k := by positivity
      have : (1 + (m : ℝ)⁻¹) * ((n : ℝ) + k)⁻¹ - (n : ℝ)⁻¹ =
          (n - k * m) / (m * n * (n + k)) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (by linarith) (by positivity)
    simp only [hw, hv, div_eq_mul_inv]
    calc a (n + k) * (n : ℝ≥0∞)⁻¹ ≤
          a (n + k) * ((1 + (m : ℝ≥0∞)⁻¹) * ((n + k : ℕ) : ℝ≥0∞)⁻¹) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun m : ℕ ↦ 1 + (m : ℝ≥0∞)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
  have hc : ∀ m : ℕ, 1 ≤ m → (1 + (m : ℝ≥0∞)⁻¹) ≠ ⊤ := fun m hm ↦
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (by exact_mod_cast
      (Nat.one_pos.trans_le hm).ne')⟩
  refine le_antisymm ?_ (limsup_le_limsup (.of_forall hvw))
  have hT := ENNReal.Tendsto.mul_const hlim (b := limsup v atTop) (Or.inl one_ne_zero)
  rw [one_mul] at hT
  refine ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun m hm ↦ ?_)
  rw [← ENNReal.limsup_const_mul_of_ne_top (hc m hm)]
  exact limsup_le_limsup (hwv m hm)

/-- At order `n ≥ 1`, the finite-scale orbit cost is at most `K^A(i) / n` for every ideal point
`x_i` of the Bowen ball `B_n(x, T, ε)` (a copy of the helper of `OrbitUpper`). -/
private theorem shiftTranslation_finiteScaleBSCost_le {X : Type*} [MetricSpace X]
    (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X)
    {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} {i : ℕ} (hi : P.ι i ∈ bowenBall T n x ε) :
    finiteScaleBSCost P T (fun _ ↦ 1) A x n ε ≤ (oracleNatComplexity A i : ℝ≥0∞) / n := by
  have hsum : birkhoffSum T (fun _ ↦ (1 : ℝ)) n (P.ι i) = n := by
    simp only [birkhoffSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hpos : 0 < birkhoffSum T (fun _ ↦ (1 : ℝ)) n (P.ι i) := by
    rw [hsum]
    exact_mod_cast hn
  unfold finiteScaleBSCost
  simp only [show n ≠ 0 by omega, ↓reduceIte]
  refine (iInf_le _ i).trans ((iInf_le _ hi).trans ((iInf_le _ hpos).trans ?_))
  rw [hsum, ENNReal.ofReal_natCast]

/-- If every ideal point `x_i` of the Bowen ball `B_n(x, T, ε)` satisfies `a ≤ K^A(i) + b`, then
`a / n ≤ K_n^A(x, T, ε)/n + b / n` (as finite-scale costs, `n ≥ 1`). -/
private theorem shiftTranslation_le_finiteScaleBSCost_add {X : Type*} [MetricSpace X]
    (P : Presentation X) (T : X → X) (A : Set ℕ) (x : X) {n : ℕ} (hn : 1 ≤ n) {ε : ℝ}
    {a b : ℕ} (h : ∀ i, P.ι i ∈ bowenBall T n x ε → a ≤ oracleNatComplexity A i + b) :
    (a : ℝ≥0∞) / n ≤ finiteScaleBSCost P T (fun _ ↦ 1) A x n ε + (b : ℝ≥0∞) / n := by
  have hsum : ∀ y, birkhoffSum T (fun _ ↦ (1 : ℝ)) n y = n := fun y ↦ by
    simp only [birkhoffSum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [← tsub_le_iff_right]
  unfold finiteScaleBSCost
  simp only [show n ≠ 0 by omega, ↓reduceIte]
  refine le_iInf fun i ↦ le_iInf fun hi ↦ le_iInf fun _ ↦ ?_
  rw [hsum, ENNReal.ofReal_natCast, tsub_le_iff_right, ← ENNReal.add_div]
  gcongr
  exact_mod_cast h i hi

/-! ### The two coding steps -/

variable {α : Type*} [Primcodable α] [MetricSpace (ℕ → α)] {β : ℝ}

/-- Upper coding: from the word `x↾m` one finds by search an ideal point in its cylinder, so
there is such a point `x_i` with `K^A(i) ≤ K^A(x↾m) + c`, as soon as the cylinder contains an
ideal point at all. -/
private theorem shiftTranslation_upper_code (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ c : ℕ, ∀ (x : ℕ → α) (m i : ℕ), P.ι i ∈ PiNat.cylinder x m → ∃ j,
      P.ι j ∈ PiNat.cylinder x m ∧ oracleNatComplexity A j ≤ wordComplexity A x m + c := by
  classical
  let G : List α × ℕ → Prop := fun q ↦ wordPrefix (P.ι q.2) q.1.length = q.1
  have hpre := shiftTranslation_computableIn_wordPrefix (f := P.ι) hP
  have hG : IsREIn A G := by
    refine isREIn_of_computableIn_decide A G ?_
    refine ((Primrec.eq.decide.to_comp : Computable₂ fun (u v : List α) ↦ decide (u = v)
      ).computableIn₂).comp
      (hpre.comp (g := fun q : List α × ℕ ↦ (q.2, q.1.length)) ?_) Computable.fst.computableIn
    exact (Computable.snd.pair (Primrec.list_length.to_comp.comp Computable.fst)).computableIn
  obtain ⟨g, hg, hgdom, hgsound⟩ := hG.exists_partrecIn_choice
  let F : ℕ →. ℕ := fun m ↦ g ((Encodable.decode m : Option (List α)).getD [])
  have hdec : Computable fun m : ℕ ↦ (Encodable.decode m : Option (List α)).getD [] :=
    Computable.option_getD Computable.decode (Computable.const [])
  have hF : PartrecIn {charOracle A} F := hg.comp hdec.computableIn
  obtain ⟨c, hc⟩ := exists_natComplexity_le_of_partrecIn A F hF
  refine ⟨c, fun x m i hi ↦ ?_⟩
  set w := wordPrefix x m with hw
  have hlen : w.length = m := shiftTranslation_length_wordPrefix x m
  have hdom : (g w).Dom := (hgdom w).2 ⟨i, by
    simp only [G, hlen]
    exact shiftTranslation_mem_cylinder_iff.1 hi⟩
  have hspec : G (w, (g w).get hdom) := hgsound w _ (Part.get_mem hdom)
  refine ⟨(g w).get hdom, ?_, ?_⟩
  · refine shiftTranslation_mem_cylinder_iff.2 ?_
    have h : wordPrefix (P.ι ((g w).get hdom)) w.length = w := hspec
    rwa [hlen] at h
  · have hFm : (g w).get hdom ∈ F (Encodable.encode w) := by
      simp only [F, Encodable.encodek, Option.getD_some]
      exact Part.get_mem hdom
    exact hc _ _ hFm

/-- Lower coding: the word `x↾m` is computed from the index `i` of any ideal point of the
cylinder `[x↾m]` and from `m`, so `K^A(x↾m) ≤ K^A(i) + K^A(m) + c`. -/
private theorem shiftTranslation_lower_code (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) :
    ∃ c : ℕ, ∀ (x : ℕ → α) (m i : ℕ), P.ι i ∈ PiNat.cylinder x m →
      wordComplexity A x m ≤ oracleNatComplexity A i + oracleNatComplexity A m + c := by
  have hpre := shiftTranslation_computableIn_wordPrefix (f := P.ι) hP
  let F : List BitString → BitString := fun xs ↦
    natBits (Encodable.encode (wordPrefix (P.ι (decodeBits (xs.getD 0 [])))
      (decodeBits (xs.getD 1 []))))
  have hget : ∀ k : ℕ, Computable (fun ws : List BitString ↦ ws.getD k []) := fun k ↦
    Computable₂.comp (f := fun (l : List BitString) (n : ℕ) ↦ l.getD n [])
      (Primrec.list_getD ([] : BitString)).to_comp Computable.id (Computable.const k)
  have hF : ComputableIn {charOracle A} F :=
    (natBits_computable.comp Computable.encode).computableIn.comp (hpre.comp
      ((decodeBits_computable.comp (hget 0)).pair
        (decodeBits_computable.comp (hget 1))).computableIn)
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A 2 (fun xs ↦ Part.some (F xs)) hF.partrecIn
  refine ⟨c, fun x m i hi ↦ ?_⟩
  have hFout : natBits (Encodable.encode (wordPrefix x m)) ∈
      Part.some (F [natBits i, natBits m]) := by
    simp only [F, List.getD_cons_zero, List.getD_cons_succ, natBits, decodeBits_natBits,
      ← shiftTranslation_mem_cylinder_iff.1 hi]
    exact Part.mem_some _
  have h := hc [natBits i, natBits m] _ rfl hFout
  simpa only [wordComplexity, oracleNatComplexity, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, add_assoc] using h

/-! ### The two translations -/

/-- Upper translation: `K̄^A(x, σ) ≤ limsup_n K^A(x↾n)/n` when the symbols of the ideal points are
`A`-computable. Blueprint node `erg:prop710`. -/
theorem orbitComplexities_snd_le_limsup_wordComplexity (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) (x : ℕ → α) :
    (orbitComplexities P shiftMap A x).2 ≤
      limsup (fun n : ℕ ↦ (wordComplexity A x n : ℝ≥0∞) / n) atTop := by
  obtain ⟨c, hc⟩ := shiftTranslation_upper_code P A hP
  have hcont := continuous_shiftMap hβ hβ₁ hd
  rw [orbitComplexities_eq_iSup_orbitComplexityAt]
  refine iSup_le fun p ↦ ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (dyadicRadius_pos p) hβ₁
  refine (orbitComplexityAt_antitone P shiftMap A x hk.le).2.trans ?_
  have hle : ∀ᶠ n : ℕ in atTop, finiteScaleBSCost P shiftMap (fun _ ↦ 1) A x n (β ^ k) ≤
      ((fun n : ℕ ↦ (wordComplexity A x (n + k) : ℝ≥0∞) / n) +
        fun n : ℕ ↦ (c : ℝ≥0∞) / n) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hball := bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd x hn k
    obtain ⟨i, hi⟩ := bowen_ball_dense P shiftMap hcont x n hn (β ^ k) (pow_pos hβ k)
    rw [hball] at hi
    obtain ⟨j, hj, hjK⟩ := hc x (n + k) i hi
    refine (shiftTranslation_finiteScaleBSCost_le P shiftMap A x hn (hball ▸ hj)).trans ?_
    rw [Pi.add_apply, ← ENNReal.add_div]
    gcongr
    exact_mod_cast hjK
  refine (limsup_le_limsup hle).trans ?_
  rw [ENNReal.limsup_add_of_right_tendsto_zero (shiftTranslation_tendsto_const_div c),
    shiftTranslation_limsup_add (fun n ↦ (wordComplexity A x n : ℝ≥0∞)) k]

/-- Lower translation: `liminf_n K^A(x↾n)/n ≤ K̲^A(x, σ)` when the symbols of the ideal points are
`A`-computable. Blueprint node `erg:prop710`. -/
theorem liminf_wordComplexity_le_orbitComplexities_fst (hβ : 0 < β) (hβ₁ : β < 1)
    (hd : ∀ x y : ℕ → α, x ≠ y → dist x y = β ^ PiNat.firstDiff x y)
    (P : Presentation (ℕ → α)) (A : Set ℕ)
    (hP : ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ P.ι q.1 q.2) (x : ℕ → α) :
    liminf (fun n : ℕ ↦ (wordComplexity A x n : ℝ≥0∞) / n) atTop ≤
      (orbitComplexities P shiftMap A x).1 := by
  obtain ⟨c, hc⟩ := shiftTranslation_lower_code P A hP
  have h1 : (1 : ℝ) = β ^ 0 := (pow_zero β).symm
  refine le_trans ?_ (orbitComplexityAt_le_orbitComplexities P shiftMap A x one_pos).1
  have hle : ∀ᶠ n : ℕ in atTop, (wordComplexity A x n : ℝ≥0∞) / n ≤
      ((fun n : ℕ ↦ finiteScaleBSCost P shiftMap (fun _ ↦ 1) A x n 1) +
        fun n : ℕ ↦ ((oracleNatComplexity A n + c : ℕ) : ℝ≥0∞) / n) n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine shiftTranslation_le_finiteScaleBSCost_add P shiftMap A x hn fun i hi ↦ ?_
    rw [h1, bowenBall_shiftMap_eq_cylinder hβ hβ₁ hd x hn 0, add_zero] at hi
    have := hc x n i hi
    omega
  refine (liminf_le_liminf hle).trans ?_
  rw [ENNReal.liminf_add_of_right_tendsto_zero
    (shiftTranslation_tendsto_natComplexity_div A c)]
  rfl

end Kolmogorov.PointToSet
