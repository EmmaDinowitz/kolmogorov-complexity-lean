/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ComputablePartition
import KolmogorovMathlib.PointToSet.Measure.Ergodic.WordRandomness

/-!
# Symbolic coding by a computable partition (Lemma 3)

Lemma 3 of the note *Orbit complexity of Martin-Löf random points equals entropy*. Let `U_1, …,
U_p` be an `A`-computable partition (`IsComputablePartitionIn`), `T` an `A`-represented map
preserving the `A`-computable probability measure `μ`, and `x` a `μ`-random point relative to `A`.

* `codingDomain T U = ⋂_k T^{-k}(⋃_j U_j)`, `symbolicCode T U x = ω` with `T^k x ∈ U_{ω_k}`
  (the itinerary), `codedMeasure μ T U = φ_* μ` with `φ = symbolicCode T U`.
* `symbolCell T U w = O_w = ⋂_{i<|w|} T^{-i} U_{w_i}` for a list word `w`
  (`symbolCell_ofFn`: it is the cell `Ergodic.refinement T U n w` for `w = List.ofFn w`);
  `isCeOpenFamilyIn_symbolCell`: the cells are `A`-c.e. open uniformly in `w` (chains of basic
  balls, `isCeOpenFamilyIn_bowenChainSet`); `symbolCell_disjoint`: cells of distinct words of
  the same length are disjoint. The itinerary satisfies `φ ∘ T = σ ∘ φ` everywhere
  (`symbolicCode_apply_map`), is measurable (`measurable_symbolicCode`), and
  `codingDomain T U` has null complement for an invariant `μ` (`measure_compl_codingDomain`).
* (i) `randomPoints_subset_codingDomain`: every random point has its whole orbit in `⋃ U_j`.
  Proof: the union of the cells `O_w`, `|w| = k + 1`, is `A`-c.e. open, contains the coding
  domain (so has null complement) and lies in `T^{-k}(⋃ U_j)`; apply
  `randomPoints_subset_of_isCeOpenIn`.
* (ii) `codedMeasure_wordCylinder` (`ν[w] = μ(⋂_{k<n} T^{-k} U_{w_k})`),
  `codedMeasure_listCylinder` (`ν[w] = μ(O_w)`), `ergodic_codedMeasure` (`ν` is shift-invariant
  and ergodic: `φ ∘ T = σ ∘ φ`), `isComputableWordMeasureIn_codedMeasure` (`ν[w] = μ(O_w)` is
  lower semicomputable uniformly in `w`, and upper semicomputable since `μ(O_w)` is the measure
  of the complement of the union `V_w` of the cells of the other words of length `|w|`), and
  `shiftEntropy_codedMeasure` (`h_ν(σ) = h_μ(T, Q)` for a measurable partition `Q ⊇ U` cellwise:
  `H_ν(ξ^n) = H_μ(Q^n)` exactly).
* (iii) `symbolicCode_mem_wordRandomPoints`: `φ(x)` is `ν`-random relative to `A`. Proof: a
  cylinder test `V_n = ⋃_{w ∈ E_n} [w]` pulls back to the `μ`-test `W_n = ⋃_{w ∈ E_n} O_w`.

Blueprint node `erg:symbolic-coding`.
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {p : ℕ}

/-- The points whose whole orbit stays in `⋃_j U_j`. Blueprint node `erg:symbolic-coding`. -/
def codingDomain (T : X → X) (U : Fin p → Set X) : Set X :=
  ⋂ k : ℕ, T^[k] ⁻¹' ⋃ j, U j

open Classical in
/-- The itinerary of `x` through the family `U`: the `k`-th symbol is the index `j` with
`T^k x ∈ U_j` (and `0` if there is none). Blueprint node `erg:symbolic-coding`. -/
noncomputable def symbolicCode [NeZero p] (T : X → X) (U : Fin p → Set X) (x : X) :
    ℕ → Fin p :=
  fun k ↦ if h : ∃ j, T^[k] x ∈ U j then h.choose else 0

/-- The coded measure `ν = φ_* μ` on `ℕ → Fin p`. Blueprint node `erg:symbolic-coding`. -/
noncomputable def codedMeasure [NeZero p] (μ : Measure X) (T : X → X) (U : Fin p → Set X) :
    Measure (ℕ → Fin p) :=
  μ.map (symbolicCode T U)

/-- The cell `O_w = ⋂_{i < |w|} T^{-i} U_{w_i}` of a finite word `w`: the points whose itinerary
through `U` begins with `w`. Blueprint node `erg:symbolic-coding`. -/
def symbolCell (T : X → X) (U : Fin p → Set X) (w : List (Fin p)) : Set X :=
  {x | ∀ i (h : i < w.length), T^[i] x ∈ U w[i]}

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The cell of the word `List.ofFn w` is the cell `⋂_{k<n} T^{-k} U_{w_k}` of the refinement.
Blueprint node `erg:symbolic-coding`. -/
theorem symbolCell_ofFn (T : X → X) (U : Fin p → Set X) {n : ℕ} (w : Fin n → Fin p) :
    symbolCell T U (List.ofFn w) = Ergodic.refinement T U n w := by
  ext x
  simp only [symbolCell, Ergodic.refinement, List.length_ofFn, List.getElem_ofFn, mem_ofPred_eq,
    mem_iInter, mem_preimage]
  exact ⟨fun h i ↦ h i i.2, fun h i hi ↦ h ⟨i, hi⟩⟩

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Cells of distinct words of the same length are disjoint when the family `U` is.
Blueprint node `erg:symbolic-coding`. -/
theorem symbolCell_disjoint {T : X → X} {U : Fin p → Set X}
    (hU : Pairwise (Function.onFun Disjoint U)) {w w' : List (Fin p)}
    (hlen : w'.length = w.length) (hne : w' ≠ w) {y : X} (h : y ∈ symbolCell T U w)
    (h' : y ∈ symbolCell T U w') : False := by
  refine hne (List.ext_getElem hlen fun i h₁ h₂ ↦ ?_)
  by_contra hij
  exact disjoint_left.mp (hU hij) (h' i h₁) (h i h₂)

omit [MeasurableSpace X] [BorelSpace X] in
/-- The members of a c.e. open family are open. -/
lemma isOpen_of_isCeOpenFamilyIn {P : Presentation X} {A : Set ℕ} {ι : Type*}
    [Primcodable ι] {V : ι → Set X} (hV : IsCeOpenFamilyIn P A V) (i : ι) : IsOpen (V i) := by
  obtain ⟨E, -, hE⟩ := hV
  rw [hE i]
  exact isOpen_biUnion fun b _ ↦ Metric.isOpen_ball

omit [MeasurableSpace X] [BorelSpace X] in
/-- The cells of the words are `A`-c.e. open, uniformly in the word, when `A` computes the
metric table, represents `T` and enumerates the family `U` uniformly. The proof feeds the step
condition "a basic ball certified inside a listed ball of `U_{w_k}`" to
`isCeOpenFamilyIn_bowenChainSet`. Blueprint node `erg:symbolic-coding`. -/
theorem isCeOpenFamilyIn_symbolCell [NeZero p] {P : Presentation X} {A : Set ℕ} {T : X → X}
    {U : Fin p → Set X} (hP : ComputablePresentationIn P A) (hTA : IsRepresentedMapIn P P A T)
    (hU : IsCeOpenFamilyIn P A U) : IsCeOpenFamilyIn P A (symbolCell T U) := by
  obtain ⟨E, hE, hUE⟩ := hU
  have hlt := birkhoff_computableIn_lt A _ hP
  obtain ⟨R', hR're, hR's, hR'small⟩ := exists_bowenChainRep P T A hP hTA
  -- step condition for the word `w` at time `k`
  let C : (List (Fin p) × ℕ) × (ℕ × ℚ) → Prop := fun v ↦
    0 < v.2.2 ∧ ∃ c : ℕ × ℚ, E (v.1.1.getD v.1.2 0, c) ∧
      dist (P.ι c.1) (P.ι v.2.1) < ((c.2 - v.2.2 : ℚ) : ℝ)
  have hCre : IsREIn A C := by
    refine (isREIn_of_computable_decide (computable₂_ratLt.comp (Computable.const 0)
      (Computable.snd.comp Computable.snd))).and ?_
    have h1 : IsREIn A fun w : ((List (Fin p) × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        E (w.1.1.1.getD w.1.1.2 0, w.2) :=
      hE.comp (((Primrec.list_getD 0).to_comp.comp
        (Computable.fst.comp (Computable.fst.comp Computable.fst))
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
          Computable.snd).computableIn
    have h2 : IsREIn A fun w : ((List (Fin p) × ℕ) × (ℕ × ℚ)) × (ℕ × ℚ) ↦
        dist (P.ι w.2.1) (P.ι w.1.2.1) < ((w.2.2 - w.1.2.2 : ℚ) : ℝ) :=
      hlt.comp (((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
        (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
          (Computable.snd.comp (Computable.snd.comp Computable.fst)))).computableIn
    exact (h1.and h2).exists
  have hCloc : ∀ a k c z, C ((a, k), c) → z ∈ basicBall P c → ∃ δ : ℝ, 0 < δ ∧
      ∀ c' : ℕ × ℚ, 0 < c'.2 → (c'.2 : ℝ) < δ → z ∈ basicBall P c' → C ((a, k), c') := by
    rintro a k c z ⟨_, c₀, hc₀, hd⟩ hz
    obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_lt (P := P) (bowenStep_dist_lt hd hz)
    exact ⟨δ, hδ, fun c' hc'0 hc'δ hzc' ↦ ⟨hc'0, c₀, hc₀, hsmall c' hc'δ hzc'⟩⟩
  have H := isCeOpenFamilyIn_bowenChainSet P T A hR're hR's hR'small hCre hCloc
  have heq : ∀ w : List (Fin p), bowenChainSet P T C w w.length = symbolCell T U w := by
    intro w
    ext y
    constructor
    · intro hy i hi
      obtain ⟨c, ⟨_, c₀, hc₀, hd⟩, hyc⟩ := hy i hi
      have hmem : T^[i] y ∈ basicBall P c₀ := by
        rw [basicBall, Metric.mem_ball, dist_comm]
        exact bowenStep_dist_lt hd hyc
      rw [← List.getD_eq_getElem _ 0 hi, hUE]
      exact mem_iUnion₂.mpr ⟨c₀, hc₀, hmem⟩
    · intro hy i hi
      have hyi := hy i hi
      rw [← List.getD_eq_getElem _ 0 hi, hUE] at hyi
      obtain ⟨c₀, hc₀, hyc₀⟩ := mem_iUnion₂.mp hyi
      have hd : dist (P.ι c₀.1) (T^[i] y) < c₀.2 := by
        rw [dist_comm]
        exact hyc₀
      obtain ⟨δ, hδ, hsmall⟩ := bowenStep_small_lt (P := P) hd
      obtain ⟨c, hc0, hcδ, hyc⟩ := bowenChain_exists_small_ball P (T^[i] y) hδ
      exact ⟨c, ⟨hc0, c₀, hc₀, hsmall c hcδ hyc⟩, hyc⟩
  have hg : Computable fun w : List (Fin p) ↦ (w, w.length) :=
    Computable.id.pair Primrec.list_length.to_comp
  have h := H.comp hg
  have hfun : symbolCell T U = fun w ↦ bowenChainSet P T C (w, w.length).1 (w, w.length).2 :=
    funext fun w ↦ (heq w).symm
  rw [hfun]
  exact h

/-- A real family with relatively enumerable strict lower and upper rational cuts is a
relatively computable real family: search for a rational interval of length `< 2^{-n}` around
the value. -/
private lemma isComputableRealFamilyIn_of_cuts {α : Type*} [Primcodable α] {A : Set ℕ}
    {v : α → ℝ} (hlo : IsREIn A fun w : α × ℚ ↦ (w.2 : ℝ) < v w.1)
    (hup : IsREIn A fun w : α × ℚ ↦ v w.1 < (w.2 : ℝ)) : IsComputableRealFamilyIn A v := by
  let G : (α × ℕ) × (ℚ × ℚ) → Prop := fun z ↦
    ((z.2.1 : ℝ) < v z.1.1 ∧ v z.1.1 < (z.2.2 : ℝ)) ∧ z.2.2 - z.2.1 < (2 ^ z.1.2 : ℚ)⁻¹
  have hG : IsREIn A G := by
    have h1 : IsREIn A fun z : (α × ℕ) × (ℚ × ℚ) ↦ ((z.2.1 : ℚ) : ℝ) < v z.1.1 :=
      hlo.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)).computableIn
    have h2 : IsREIn A fun z : (α × ℕ) × (ℚ × ℚ) ↦ v z.1.1 < ((z.2.2 : ℚ) : ℝ) :=
      hup.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.comp Computable.snd)).computableIn
    have h3 : IsREIn A fun z : (α × ℕ) × (ℚ × ℚ) ↦ z.2.2 - z.2.1 < (2 ^ z.1.2 : ℚ)⁻¹ :=
      isREIn_of_computable_decide (computable₂_ratLt.comp
        (computable₂_ratSub.comp (Computable.snd.comp Computable.snd)
          (Computable.fst.comp Computable.snd))
        (computable_rat_inv_two_pow.comp (Computable.snd.comp Computable.fst)))
    exact (h1.and h2).and h3
  have htot : ∀ a : α × ℕ, ∃ b : ℚ × ℚ, G (a, b) := by
    rintro ⟨i, n⟩
    have hε : (0 : ℝ) < (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) := by positivity
    obtain ⟨a, ha1, ha2⟩ :=
      exists_rat_btwn (show v i - (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) / 2 < v i by linarith)
    obtain ⟨b, hb1, hb2⟩ :=
      exists_rat_btwn (show v i < v i + (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) / 2 by linarith)
    refine ⟨(a, b), ⟨ha2, hb1⟩, ?_⟩
    have h : ((b - a : ℚ) : ℝ) < (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) := by
      push_cast at ha1 hb2 ⊢
      linarith
    exact_mod_cast h
  obtain ⟨g, hg, hgG⟩ := hG.exists_computableIn_choice htot
  refine ⟨fun z ↦ (g z).1, (Computable.fst (α := ℚ) (β := ℚ)).computableIn.comp hg, fun i n ↦ ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hgG (i, n)
  have h3' : (((g (i, n)).2 : ℚ) : ℝ) - (((g (i, n)).1 : ℚ) : ℝ) < (2 : ℝ)⁻¹ ^ n := by
    have h4 : ((((g (i, n)).2 - (g (i, n)).1 : ℚ)) : ℝ) < (((2 ^ n : ℚ)⁻¹ : ℚ) : ℝ) :=
      Rat.cast_lt.mpr h3
    push_cast at h4
    rwa [inv_pow]
  rw [abs_sub_lt_iff]
  constructor <;> linarith

variable [NeZero p] {P : Presentation X} {A : Set ℕ} {μ : Measure X} {T : X → X}
  {U : Fin p → Set X}

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- For a pairwise disjoint family, `T^k x ∈ U_j` forces the `k`-th symbol to be `j` (with no
assumption on the rest of the orbit). Blueprint node `erg:symbolic-coding`. -/
theorem symbolicCode_eq_of_mem (hU : Pairwise (Function.onFun Disjoint U)) {x : X} {k : ℕ}
    {j : Fin p} (h : T^[k] x ∈ U j) : symbolicCode T U x k = j := by
  have hex : ∃ j, T^[k] x ∈ U j := ⟨j, h⟩
  simp only [symbolicCode, dite_eq_left hex]
  by_contra hne
  exact disjoint_left.mp (hU hne) hex.choose_spec h

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- On the coding domain the itinerary is correct: `T^k x ∈ U_{φ(x)_k}`.
Blueprint node `erg:symbolic-coding`. -/
theorem iterate_mem_symbolicCode (hU : Pairwise (Function.onFun Disjoint U)) {x : X}
    (hx : x ∈ codingDomain T U) (k : ℕ) : T^[k] x ∈ U (symbolicCode T U x k) := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp (mem_iInter.mp hx k)
  rw [symbolicCode_eq_of_mem hU hj]
  exact hj

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The fibres of the `k`-th symbol: `φ(x)_k = j` iff `T^k x ∈ U_j`, or `j = 0` and `T^k x`
lies in no `U_i`. Blueprint node `erg:symbolic-coding`. -/
theorem symbolicCode_eq_iff (hU : Pairwise (Function.onFun Disjoint U)) (x : X) (k : ℕ)
    (j : Fin p) :
    symbolicCode T U x k = j ↔ T^[k] x ∈ U j ∨ (j = 0 ∧ T^[k] x ∉ ⋃ i, U i) := by
  by_cases hex : ∃ i, T^[k] x ∈ U i
  · obtain ⟨i, hi⟩ := hex
    rw [symbolicCode_eq_of_mem hU hi]
    constructor
    · rintro rfl
      exact Or.inl hi
    · rintro (h | ⟨-, h⟩)
      · by_contra hne
        exact disjoint_left.mp (hU hne) hi h
      · exact absurd (mem_iUnion.mpr ⟨i, hi⟩) h
  · have h0 : symbolicCode T U x k = 0 := by
      simp only [symbolicCode, dite_eq_right hex]
    have hu : T^[k] x ∉ ⋃ i, U i := fun h ↦ hex (mem_iUnion.mp h)
    rw [h0]
    constructor
    · rintro rfl
      exact Or.inr ⟨rfl, hu⟩
    · rintro (h | ⟨rfl, -⟩)
      · exact absurd ⟨j, h⟩ hex
      · rfl

omit [MetricSpace X] [BorelSpace X] in
/-- The itinerary map is measurable for a measurable `T` and a disjoint family of measurable
sets. Blueprint node `erg:symbolic-coding`. -/
theorem measurable_symbolicCode (hT : Measurable T) (hUm : ∀ j, MeasurableSet (U j))
    (hU : Pairwise (Function.onFun Disjoint U)) : Measurable (symbolicCode T U) := by
  rw [measurable_pi_iff]
  intro k
  refine measurable_to_countable' fun j ↦ ?_
  have heq : (fun x ↦ symbolicCode T U x k) ⁻¹' {j} =
      T^[k] ⁻¹' U j ∪ {_x | j = 0} ∩ (T^[k] ⁻¹' ⋃ i, U i)ᶜ := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, symbolicCode_eq_iff hU, mem_union, mem_inter_iff,
      mem_ofPred_eq, mem_compl_iff]
  rw [heq]
  exact ((hT.iterate k) (hUm j)).union ((MeasurableSet.const _).inter
    ((hT.iterate k) (MeasurableSet.iUnion hUm)).compl)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The itinerary conjugates `T` to the shift, everywhere: `φ (T x) = σ (φ x)`.
Blueprint node `erg:symbolic-coding`. -/
theorem symbolicCode_apply_map (x : X) :
    symbolicCode T U (T x) = shiftMap (symbolicCode T U x) := by
  funext k
  simp only [symbolicCode, shiftMap, ← Function.iterate_succ_apply]
  rfl

omit [NeZero p] in
/-- The shift is measurable. -/
private lemma measurable_shiftMap' : Measurable (shiftMap : (ℕ → Fin p) → ℕ → Fin p) :=
  measurable_pi_iff.mpr fun j ↦ measurable_pi_apply (j + 1)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The points of a cell have itineraries in the corresponding cylinder.
Blueprint node `erg:symbolic-coding`. -/
theorem symbolCell_subset_preimage (hU : Pairwise (Function.onFun Disjoint U))
    (w : List (Fin p)) : symbolCell T U w ⊆ symbolicCode T U ⁻¹' listCylinder w :=
  fun _ hx i hi ↦ symbolicCode_eq_of_mem hU (hx i hi)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- On the coding domain a point lies in the cell of every word its itinerary begins with.
Blueprint node `erg:symbolic-coding`. -/
theorem mem_symbolCell_of_mem_codingDomain (hU : Pairwise (Function.onFun Disjoint U)) {x : X}
    (hx : x ∈ codingDomain T U) {w : List (Fin p)} (hw : symbolicCode T U x ∈ listCylinder w) :
    x ∈ symbolCell T U w := by
  intro i hi
  rw [← hw i hi]
  exact iterate_mem_symbolicCode hU hx i

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- On the coding domain a point lies in the cell of each prefix of its itinerary.
Blueprint node `erg:symbolic-coding`. -/
theorem mem_symbolCell_wordPrefix (hU : Pairwise (Function.onFun Disjoint U)) {x : X}
    (hx : x ∈ codingDomain T U) (n : ℕ) :
    x ∈ symbolCell T U (wordPrefix (symbolicCode T U x) n) :=
  mem_symbolCell_of_mem_codingDomain hU hx (mem_listCylinder_wordPrefix _ n)

omit [MetricSpace X] [BorelSpace X] [NeZero p] in
/-- For an invariant measure, the coding domain has null complement as soon as `⋃_j U_j` has.
Blueprint node `erg:symbolic-coding`. -/
theorem measure_compl_codingDomain (hT : MeasurePreserving T μ μ)
    (hUm : ∀ j, MeasurableSet (U j)) (hnull : μ (⋃ j, U j)ᶜ = 0) :
    μ (codingDomain T U)ᶜ = 0 := by
  rw [codingDomain, compl_iInter]
  refine measure_iUnion_null fun k ↦ ?_
  rw [← preimage_compl,
    (hT.iterate k).measure_preimage (MeasurableSet.iUnion hUm).compl.nullMeasurableSet]
  exact hnull

omit [NeZero p] in
/-- The cells of a computable partition are measurable. -/
private lemma measurableSet_of_isComputablePartitionIn (hU : IsComputablePartitionIn P A μ U)
    (j : Fin p) : MeasurableSet (U j) :=
  (isOpen_of_isCeOpenFamilyIn hU.1 j).measurableSet

/-- Lemma 3(i): every point that is `μ`-random relative to `A` lies in the coding domain.
Blueprint node `erg:symbolic-coding`. -/
theorem randomPoints_subset_codingDomain [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (hT : MeasurePreserving T μ μ)
    (hU : IsComputablePartitionIn P A μ U) : randomPoints P A μ ⊆ codingDomain T U := by
  obtain ⟨hP, hTA, hμ⟩ := hA
  have hD := measure_compl_codingDomain hT (measurableSet_of_isComputablePartitionIn hU) hU.2.2
  obtain ⟨E, hE, hEO⟩ := isCeOpenFamilyIn_symbolCell hP hTA hU.1
  intro x hx
  refine mem_iInter.mpr fun k ↦ ?_
  -- the union of the cells of the words of length `k + 1`
  let G : Set X :=
    ⋃ b ∈ {b | ∃ w : List (Fin p), w.length = k + 1 ∧ E (w, b)}, basicBall P b
  have hG : IsCeOpenIn P A G := by
    have h1 : IsREIn A fun v : (ℕ × ℚ) × List (Fin p) ↦ v.2.length = k + 1 :=
      isREIn_of_computable_decide (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.const (k + 1))).decide.to_comp
    have h2 : IsREIn A fun v : (ℕ × ℚ) × List (Fin p) ↦ E (v.2, v.1) :=
      hE.comp (Computable.snd.pair Computable.fst).computableIn
    have hre : IsREIn A fun b ↦ ∃ w : List (Fin p), w.length = k + 1 ∧ E (w, b) :=
      (h1.and h2).exists
    exact ⟨_, hre, rfl⟩
  have hmemG : ∀ {y : X} {w : List (Fin p)}, w.length = k + 1 → y ∈ symbolCell T U w →
      y ∈ G := by
    intro y w hw hy
    rw [hEO w] at hy
    obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨b, ⟨w, hw, hb⟩, hyb⟩
  have hDG : codingDomain T U ⊆ G := fun y hy ↦
    hmemG (by simp [wordPrefix]) (mem_symbolCell_wordPrefix hU.2.1 hy (k + 1))
  have hxG : x ∈ G :=
    randomPoints_subset_of_isCeOpenIn P A μ hP hμ hG
      (measure_mono_null (compl_subset_compl.mpr hDG) hD) hx
  obtain ⟨b, ⟨w, hw, hb⟩, hxb⟩ := mem_iUnion₂.mp hxG
  have hxw : x ∈ symbolCell T U w := by
    rw [hEO w]
    exact mem_iUnion₂.mpr ⟨b, hb, hxb⟩
  have hk : k < w.length := by omega
  exact mem_iUnion.mpr ⟨_, hxw k hk⟩

/-- Lemma 3(ii), list form: `ν[w] = μ(O_w)`. Blueprint node `erg:symbolic-coding`. -/
theorem codedMeasure_listCylinder (hT : MeasurePreserving T μ μ)
    (hU : IsComputablePartitionIn P A μ U) (w : List (Fin p)) :
    codedMeasure μ T U (listCylinder w) = μ (symbolCell T U w) := by
  have hUm := measurableSet_of_isComputablePartitionIn hU
  have hφ := measurable_symbolicCode hT.measurable hUm hU.2.1
  have hD := measure_compl_codingDomain hT hUm hU.2.2
  rw [codedMeasure, Measure.map_apply hφ (measurableSet_listCylinder w)]
  refine le_antisymm ?_ (measure_mono (symbolCell_subset_preimage hU.2.1 w))
  have hsub : symbolicCode T U ⁻¹' listCylinder w ⊆ symbolCell T U w ∪ (codingDomain T U)ᶜ := by
    intro y hy
    by_cases hyD : y ∈ codingDomain T U
    · exact Or.inl (mem_symbolCell_of_mem_codingDomain hU.2.1 hyD hy)
    · exact Or.inr hyD
  calc μ (symbolicCode T U ⁻¹' listCylinder w)
      ≤ μ (symbolCell T U w ∪ (codingDomain T U)ᶜ) := measure_mono hsub
    _ ≤ μ (symbolCell T U w) + μ (codingDomain T U)ᶜ := measure_union_le _ _
    _ = μ (symbolCell T U w) := by rw [hD, add_zero]

/-- Lemma 3(ii): the coded measure of a cylinder is the measure of the corresponding cell
`⋂_{k<n} T^{-k} U_{w_k}`. Blueprint node `erg:symbolic-coding`. -/
theorem codedMeasure_wordCylinder [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hU : IsComputablePartitionIn P A μ U) {n : ℕ} (w : Fin n → Fin p) :
    codedMeasure μ T U (wordCylinder w) = μ (Ergodic.refinement T U n w) := by
  rw [← listCylinder_ofFn, codedMeasure_listCylinder hT hU, symbolCell_ofFn]

/-- Lemma 3(ii): the coded measure is a shift-invariant ergodic probability measure.
Blueprint node `erg:symbolic-coding`. -/
theorem ergodic_codedMeasure [IsProbabilityMeasure μ] (hT : Ergodic T μ)
    (hU : IsComputablePartitionIn P A μ U) : Ergodic shiftMap (codedMeasure μ T U) := by
  have hφ := measurable_symbolicCode hT.toMeasurePreserving.measurable
    (measurableSet_of_isComputablePartitionIn hU) hU.2.1
  have hmp : MeasurePreserving (symbolicCode T U) μ (codedMeasure μ T U) := ⟨hφ, rfl⟩
  exact hmp.ergodic_of_ergodic_semiconj hT measurable_shiftMap' fun x ↦ symbolicCode_apply_map x

/-- The coded measure is a probability measure. Blueprint node `erg:symbolic-coding`. -/
theorem isProbabilityMeasure_codedMeasure [IsProbabilityMeasure μ] (hT : Measurable T)
    (hU : IsComputablePartitionIn P A μ U) : IsProbabilityMeasure (codedMeasure μ T U) := by
  have hφ := measurable_symbolicCode hT (measurableSet_of_isComputablePartitionIn hU) hU.2.1
  exact (Measure.isProbabilityMeasure_map_iff hφ.aemeasurable).mpr inferInstance

/-- Lemma 3(ii): the coded measure is `A`-computable on cylinders.
Blueprint node `erg:symbolic-coding`. -/
theorem isComputableWordMeasureIn_codedMeasure [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (hT : MeasurePreserving T μ μ)
    (hU : IsComputablePartitionIn P A μ U) : IsComputableWordMeasureIn A (codedMeasure μ T U) := by
  obtain ⟨hP, hTA, hμ⟩ := hA
  have hUm := measurableSet_of_isComputablePartitionIn hU
  have hD := measure_compl_codingDomain hT hUm hU.2.2
  have hcell := isCeOpenFamilyIn_symbolCell hP hTA hU.1
  obtain ⟨E, hE, hEO⟩ := hcell
  -- the union of the cells of the other words of the same length
  let V : List (Fin p) → Set X := fun w ↦
    ⋃ b ∈ {b | ∃ w' : List (Fin p), (w'.length = w.length ∧ w' ≠ w) ∧ E (w', b)}, basicBall P b
  have hV : IsCeOpenFamilyIn P A V := by
    have h1 : IsREIn A fun v : (List (Fin p) × (ℕ × ℚ)) × List (Fin p) ↦
        v.2.length = v.1.1.length ∧ v.2 ≠ v.1.1 :=
      isREIn_of_computable_decide (PrimrecPred.and
        (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.eq.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).not).decide.to_comp
    have h2 : IsREIn A fun v : (List (Fin p) × (ℕ × ℚ)) × List (Fin p) ↦ E (v.2, v.1.2) :=
      hE.comp (Computable.snd.pair (Computable.snd.comp Computable.fst)).computableIn
    have hre : IsREIn A fun wb : List (Fin p) × (ℕ × ℚ) ↦ ∃ w' : List (Fin p),
        (w'.length = wb.1.length ∧ w' ≠ wb.1) ∧ E (w', wb.2) :=
      (h1.and h2).exists
    exact ⟨_, hre, fun w ↦ rfl⟩
  have hcompl : ∀ w, μ (V w)ᶜ = μ (symbolCell T U w) := by
    intro w
    have hcellV : ∀ {y : X} {w' : List (Fin p)}, y ∈ symbolCell T U w' → y ∈ ⋃ b ∈
        {b | E (w', b)}, basicBall P b := fun hy ↦ by rwa [← hEO]
    refine le_antisymm ?_ (measure_mono fun y hy hyV ↦ ?_)
    · have hsub : (V w)ᶜ ⊆ symbolCell T U w ∪ (codingDomain T U)ᶜ := by
        intro y hy
        by_cases hyD : y ∈ codingDomain T U
        · left
          set w' := wordPrefix (symbolicCode T U y) w.length
          have hyw' : y ∈ symbolCell T U w' := mem_symbolCell_wordPrefix hU.2.1 hyD w.length
          by_cases hww : w' = w
          · rwa [hww] at hyw'
          · exfalso
            obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp (hcellV hyw')
            exact hy (mem_iUnion₂.mpr ⟨b, ⟨w', ⟨by simp [w', wordPrefix], hww⟩, hb⟩, hyb⟩)
        · exact Or.inr hyD
      calc μ (V w)ᶜ ≤ μ (symbolCell T U w ∪ (codingDomain T U)ᶜ) := measure_mono hsub
        _ ≤ μ (symbolCell T U w) + μ (codingDomain T U)ᶜ := measure_union_le _ _
        _ = μ (symbolCell T U w) := by rw [hD, add_zero]
    · obtain ⟨b, ⟨w', ⟨hlen, hne⟩, hb⟩, hyb⟩ := mem_iUnion₂.mp hyV
      have hyw' : y ∈ symbolCell T U w' := by
        rw [hEO]
        exact mem_iUnion₂.mpr ⟨b, hb, hyb⟩
      exact symbolCell_disjoint hU.2.1 hlen hne hy hyw'
  have hlo := hμ.lowerSemicomputable_ceOpen (U := symbolCell T U) ⟨E, hE, hEO⟩
  have hup := hμ.isREIn_measure_compl_lt hV
  have hfun : (fun w : List (Fin p) ↦ (codedMeasure μ T U (listCylinder w)).toReal) =
      fun w ↦ (μ (symbolCell T U w)).toReal :=
    funext fun w ↦ by rw [codedMeasure_listCylinder hT hU]
  unfold IsComputableWordMeasureIn
  rw [hfun]
  refine isComputableRealFamilyIn_of_cuts hlo ?_
  simpa only [hcompl] using hup

/-- Lemma 3(ii): `h_ν(σ) = h_μ(T, Q)` for a measurable partition `Q` containing `U` cellwise.
Blueprint node `erg:symbolic-coding`. -/
theorem shiftEntropy_codedMeasure [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hU : IsComputablePartitionIn P A μ U) {Q : Fin p → Set X}
    (hQ : Ergodic.IsMeasurablePartition Q) (hUQ : ∀ j, U j ⊆ Q j) :
    shiftEntropy (codedMeasure μ T U) = Ergodic.entropyRate μ T Q := by
  have hblock : ∀ k, blockEntropy (codedMeasure μ T U) k = Ergodic.refinementEntropy μ T Q k := by
    intro k
    rw [← Ergodic.refinementEntropy_congr_ae hT
      (fun j ↦ ae_eq_of_isComputablePartitionIn hU hQ hUQ j) k]
    simp only [blockEntropy, Ergodic.refinementEntropy, Ergodic.partitionEntropy,
      Ergodic.entropyTerm, codedMeasure_wordCylinder hT hU]
  simp only [shiftEntropy, Ergodic.entropyRate, hblock]

/-- Lemma 3(iii): the itinerary of a `μ`-random point is `ν`-random relative to the same oracle.
Blueprint node `erg:symbolic-coding`. -/
theorem symbolicCode_mem_wordRandomPoints [IsProbabilityMeasure μ]
    (hA : IsMeasureAdmissible P T μ A) (hT : MeasurePreserving T μ μ)
    (hU : IsComputablePartitionIn P A μ U) {x : X} (hx : x ∈ randomPoints P A μ) :
    symbolicCode T U x ∈ wordRandomPoints A (codedMeasure μ T U) := by
  have hxD := randomPoints_subset_codingDomain hA hT hU hx
  obtain ⟨hP, hTA, -⟩ := hA
  have hφ := measurable_symbolicCode hT.measurable
    (measurableSet_of_isComputablePartitionIn hU) hU.2.1
  rintro V ⟨E, hE, hVE, hVμ⟩
  obtain ⟨EO, hEO, hO⟩ := isCeOpenFamilyIn_symbolCell hP hTA hU.1
  -- the pulled-back test `W_m = ⋃_{w ∈ E_m} O_w`
  let W : ℕ → Set X := fun m ↦ ⋃ w ∈ {w | E (m, w)}, symbolCell T U w
  have hW : IsCeOpenFamilyIn P A W := by
    have h1 : IsREIn A fun v : (ℕ × (ℕ × ℚ)) × List (Fin p) ↦ E (v.1.1, v.2) :=
      hE.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    have h2 : IsREIn A fun v : (ℕ × (ℕ × ℚ)) × List (Fin p) ↦ EO (v.2, v.1.2) :=
      hEO.comp (Computable.snd.pair (Computable.snd.comp Computable.fst)).computableIn
    have hre : IsREIn A fun mb : ℕ × (ℕ × ℚ) ↦ ∃ w, E (mb.1, w) ∧ EO (w, mb.2) :=
      (h1.and h2).exists
    refine ⟨_, hre, fun m ↦ ?_⟩
    · ext y
      simp only [W, mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨w, hw, hy⟩
        rw [hO w] at hy
        obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hy
        exact ⟨b, ⟨w, hw, hb⟩, hyb⟩
      · rintro ⟨b, ⟨w, hw, hb⟩, hyb⟩
        refine ⟨w, hw, ?_⟩
        rw [hO w]
        exact mem_iUnion₂.mpr ⟨b, hb, hyb⟩
  have hWμ : ∀ m, μ (W m) ≤ (2 : ℝ≥0∞)⁻¹ ^ m := by
    intro m
    refine le_trans (measure_mono ?_) ((Measure.le_map_apply hφ.aemeasurable (V m)).trans
      (hVμ m))
    intro y hy
    obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hy
    rw [mem_preimage, hVE m]
    exact mem_iUnion₂.mpr ⟨w, hw, symbolCell_subset_preimage hU.2.1 w hyw⟩
  obtain ⟨m, hm⟩ := hx W ⟨hW, hWμ⟩
  refine ⟨m, fun hmem ↦ hm ?_⟩
  rw [hVE m] at hmem
  obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hmem
  exact mem_iUnion₂.mpr ⟨w, hw, mem_symbolCell_of_mem_codingDomain hU.2.1 hxD hxw⟩

end Kolmogorov.PointToSet
