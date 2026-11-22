/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Measure.Ergodic.ShiftRandomness
import KolmogorovMathlib.PointToSet.Measure.Ergodic.HoyrupPoincareAux

/-!
# A computable presentation of Cantor space

On Cantor space `ℕ → Bool` with the metric `cantorMetricSpace` (`d(x, y) = (1/2)^{firstDiff x y}`,
a local instance) this file fixes the presentation `cantorPresentation` whose ideal points are
the eventually-`false` sequences `w 0^∞`, enumerated through `Encodable.decode : ℕ → List Bool`.

* `cantorPres_computablePresentationIn`, `cantorPres_computableIn_symbols`,
  `cantorPres_isRepresentedMapIn_shiftMap`: for every oracle `A` the metric table is
  `A`-computable (the ideal distances are computable rationals), the symbols of the ideal points
  are computable, and the shift is represented.
* `cantorPres_basicBall_eq`: every basic ball is a decidable union of cylinders.
* `cantorPres_isMeasureAdmissible`: a finite measure with `A`-computable cylinder measures is
  admissible for `(ℕ → Bool, d, σ, μ)` relative to `A`.
* `cantorPres_randomPoints_eq`: randomness for the presentation is randomness for cylinder tests.
* `cantorPres_mem_wordRandomPoints_of_isMartinLofRandom`: Martin-Löf randomness in the sense of
  `AlgorithmicRandomness` implies cylinder-test randomness relative to the empty oracle.
* Transfer along a causal map `f` given on words by a computable `F` with
  `f(y)↾n = F(y↾n)`: `cantorPres_map_mem_wordRandomPoints` (randomness is preserved) and
  `cantorPres_isComputableWordMeasureIn_map` (cylinder computability is preserved: the measure
  `λ(f⁻¹[w])` is the finite sum of `λ[v]` over the words `v` of length `|w|` with `F v = w`).
  A length-preserving monotone word map `F` induces such an `f`, `CantorPres.seqMap F`
  (`cantorPres_wordPrefix_seqMap`); `cantorPres_causal`, `cantorPres_measurable` and
  `cantorPres_map_cylinder` restate the hypotheses of the helpers of `RandomNonAtom`.
* `cantorPres_isMeasureAdmissible_map_uniformMeasure`,
  `cantorPres_map_mem_randomPoints_of_isMartinLofRandom`: for the fair-coin measure `λ` the image
  `λ ∘ f⁻¹` is admissible relative to every oracle, and `f` maps Martin-Löf random sequences to
  `λ ∘ f⁻¹`-random points.

Blueprint node `meas:examples` (infrastructure for Example 5.5).
-/

namespace Kolmogorov.PointToSet

open Filter Set MeasureTheory
open scoped Topology ENNReal Computability

attribute [local instance] cantorMetricSpace

namespace CantorPres

/-! ### Words, ideal points and their distances -/

/-- The binary word coded by `n` (the empty word when `n` codes no word). -/
def word (n : ℕ) : List Bool := (Encodable.decode n).getD []

/-- The eventually-`false` sequence `w 0^∞`. -/
def pad (w : List Bool) : ℕ → Bool := fun i ↦ w.getD i false

/-- The first index below `max |u| |v|` where `pad u` and `pad v` differ (this maximum when
there is none). -/
def diffIdx (u v : List Bool) : ℕ :=
  (List.range (max u.length v.length)).findIdx fun i ↦ decide (u.getD i false ≠ v.getD i false)

/-- The distance between `pad u` and `pad v`, as a rational. -/
def distQ (u v : List Bool) : ℚ :=
  if diffIdx u v < max u.length v.length then (2 : ℚ)⁻¹ ^ diffIdx u v else 0

/-- The word of the code of `w` is `w`. -/
@[simp] lemma word_encode (w : List Bool) : word (Encodable.encode w) = w := by
  simp [word]

/-- The padded sequence of a word extends the word. -/
lemma pad_mem_listCylinder (w : List Bool) : pad w ∈ listCylinder w := by
  intro i hi
  simp [pad, List.getElem?_eq_getElem hi]

/-- The padded sequence of `x↾n` agrees with `x` below `n`. -/
lemma pad_wordPrefix_of_lt (x : ℕ → Bool) {n i : ℕ} (hi : i < n) :
    pad (wordPrefix x n) i = x i := by
  simp [pad, wordPrefix, hi]

/-- Shifting a padded word is padding its tail. -/
lemma shiftMap_pad (w : List Bool) : shiftMap (pad w) = pad w.tail := by
  funext i
  cases w with
  | nil => simp [shiftMap, pad]
  | cons b w => simp [shiftMap, pad]

/-! ### The Cantor metric -/

/-- The Cantor metric with ratio `2⁻¹`. -/
lemma dist_eq_of_ne {x y : ℕ → Bool} (h : x ≠ y) :
    dist x y = (2 : ℝ)⁻¹ ^ PiNat.firstDiff x y := by
  rw [cantorMetricSpace_dist_eq h, one_div]

/-- `d(x, y) < 2^{-k}` iff `x` and `y` agree up to the index `k`. -/
lemma dist_lt_pow_iff {x y : ℕ → Bool} {k : ℕ} :
    dist x y < (2 : ℝ)⁻¹ ^ k ↔ ∀ i ≤ k, x i = y i := by
  constructor
  · intro h i hi
    by_cases hxy : x = y
    · rw [hxy]
    rw [dist_eq_of_ne hxy] at h
    refine PiNat.apply_eq_of_lt_firstDiff (lt_of_not_ge fun hle ↦ ?_)
    exact h.not_ge (pow_le_pow_of_le_one (by norm_num) (by norm_num) (hle.trans hi))
  · intro h
    by_cases hxy : x = y
    · rw [hxy, dist_self]
      positivity
    rw [dist_eq_of_ne hxy]
    have hk : k + 1 ≤ PiNat.firstDiff x y := by
      by_contra hlt
      exact PiNat.apply_firstDiff_ne hxy (h _ (by omega))
    calc (2 : ℝ)⁻¹ ^ PiNat.firstDiff x y ≤ (2 : ℝ)⁻¹ ^ (k + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ < (2 : ℝ)⁻¹ ^ k := pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) k.lt_succ_self

/-- Two sequences that agree below `k` are at distance at most `2^{-k}`. -/
lemma dist_le_pow {x y : ℕ → Bool} {k : ℕ} (h : ∀ i < k, x i = y i) :
    dist x y ≤ (2 : ℝ)⁻¹ ^ k := by
  by_cases hxy : x = y
  · rw [hxy, dist_self]
    positivity
  rw [dist_eq_of_ne hxy]
  refine pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_not_gt fun hlt ↦ ?_)
  exact PiNat.apply_firstDiff_ne hxy (h _ hlt)

/-- A point of the cylinder `[w]` is at distance at most `2^{-|w|}` from `pad w`. -/
lemma dist_pad_le {w : List Bool} {y : ℕ → Bool} (hy : y ∈ listCylinder w) :
    dist y (pad w) ≤ (2 : ℝ)⁻¹ ^ w.length :=
  dist_le_pow fun i hi ↦ by rw [hy i hi]; simp [pad, List.getElem?_eq_getElem hi]

/-- The rational distance `distQ` is the distance of the padded sequences. -/
lemma dist_pad (u v : List Bool) : dist (pad u) (pad v) = (distQ u v : ℝ) := by
  set N := max u.length v.length with hN
  have hbig : ∀ i, N ≤ i → pad u i = pad v i := by
    intro i hi
    simp only [pad]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  by_cases huv : pad u = pad v
  · have hidx : diffIdx u v = N := by
      have h := (List.findIdx_eq_length (p := fun i ↦ decide (u.getD i false ≠ v.getD i false))
        (xs := List.range N)).mpr fun i _ ↦ by
          have := congrFun huv i
          simpa [pad] using this
      simpa [diffIdx, hN] using h
    rw [huv, dist_self, distQ, ← hN, hidx]
    simp
  · set j := PiNat.firstDiff (pad u) (pad v) with hj
    have hjne : pad u j ≠ pad v j := PiNat.apply_firstDiff_ne huv
    have hjN : j < N := lt_of_not_ge fun h ↦ hjne (hbig j h)
    have hidx : diffIdx u v = j := by
      have hlen : j < (List.range N).length := by simpa using hjN
      refine (List.findIdx_eq hlen).mpr ⟨?_, fun k hk ↦ ?_⟩
      · simpa [pad] using hjne
      · have hk' : pad u k = pad v k := PiNat.apply_eq_of_lt_firstDiff hk
        simpa [pad] using hk'
    rw [dist_eq_of_ne huv, distQ, ← hN, hidx, ← hj]
    simp only [hjN, ↓reduceIte]
    push_cast
    rfl

/-- The rational `2^{-k}` cast to the reals. -/
lemma cast_inv_two_pow_real (k : ℕ) : (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ k := by
  push_cast
  rfl

/-! ### Computability of the finite data -/

/-- `word` is computable. -/
lemma computable_word : Computable word :=
  Computable.option_getD Computable.decode (Computable.const [])

/-- The symbols of padded words are primitive recursive. -/
lemma primrec_getD : Primrec₂ fun (w : List Bool) (i : ℕ) ↦ w.getD i false :=
  Primrec.list_getD false

/-- `diffIdx` is primitive recursive. -/
lemma primrec_diffIdx : Primrec₂ diffIdx := by
  have hN : Primrec fun uv : List Bool × List Bool ↦ max uv.1.length uv.2.length :=
    Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)
  have hp : Primrec₂ fun (uv : List Bool × List Bool) (i : ℕ) ↦
      decide (uv.1.getD i false ≠ uv.2.getD i false) :=
    (PrimrecPred.not (Primrec.eq.comp (primrec_getD.comp (Primrec.fst.comp Primrec.fst)
      Primrec.snd) (primrec_getD.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))).decide
  exact Primrec.list_findIdx (Primrec.list_range.comp hN) hp

/-- `distQ` is computable. -/
lemma computable_distQ : Computable₂ distQ := by
  have hN : Primrec fun uv : List Bool × List Bool ↦ max uv.1.length uv.2.length :=
    Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp Primrec.snd)
  have hd : Primrec fun uv : List Bool × List Bool ↦ diffIdx uv.1 uv.2 :=
    primrec_diffIdx.comp Primrec.fst Primrec.snd
  have hc : Computable fun uv : List Bool × List Bool ↦
      decide (diffIdx uv.1 uv.2 < max uv.1.length uv.2.length) :=
    (Primrec.nat_lt.comp hd hN).decide.to_comp
  refine (Computable.cond hc (computable_inv_two_pow.comp hd.to_comp)
    (Computable.const (0 : ℚ))).of_eq fun uv ↦ ?_
  simp only [distQ]
  split_ifs with h <;> simp [h]

end CantorPres

open CantorPres

/-! ### The presentation -/

/-- The presentation of Cantor space by the eventually-`false` sequences: the `n`-th ideal point
is `w 0^∞` for the word `w` coded by `n`. Blueprint node `meas:examples`. -/
noncomputable def cantorPresentation : Presentation (ℕ → Bool) where
  ι n := pad (word n)
  dense := by
    rw [Metric.denseRange_iff]
    intro x ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨Encodable.encode (wordPrefix x N), ?_⟩
    rw [word_encode]
    exact (dist_le_pow fun i hi ↦ (pad_wordPrefix_of_lt x hi).symm).trans_lt hN
  complete := inferInstance

/-- The ideal points of `cantorPresentation`. -/
lemma cantorPres_ι (n : ℕ) : cantorPresentation.ι n = pad (word n) := rfl

/-- The ideal point coded by a word is the padded word. -/
lemma cantorPres_ι_encode (w : List Bool) :
    cantorPresentation.ι (Encodable.encode w) = pad w := by
  rw [cantorPres_ι, word_encode]

/-- The symbols of the ideal points are computable. Blueprint node `meas:examples`. -/
theorem cantorPres_computableIn_symbols (A : Set ℕ) :
    ComputableIn {charOracle A} fun q : ℕ × ℕ ↦ cantorPresentation.ι q.1 q.2 :=
  ((primrec_getD.to_comp.comp (computable_word.comp Computable.fst)
    Computable.snd)).computableIn

/-- The metric table of `cantorPresentation` is computable, relative to every oracle.
Blueprint node `meas:examples`. -/
theorem cantorPres_computablePresentationIn (A : Set ℕ) :
    ComputablePresentationIn cantorPresentation A := by
  refine ⟨fun z ↦ distQ (word z.1.1) (word z.1.2), ?_, fun ij p ↦ ?_⟩
  · exact (computable_distQ.comp (computable_word.comp (Computable.fst.comp Computable.fst))
      (computable_word.comp (Computable.snd.comp Computable.fst))).computableIn
  · simp only [cantorPres_ι, dist_pad, sub_self, abs_zero]
    positivity

namespace CantorPres

/-! ### The shift is represented -/

/-- The decidable kernel of the relation representing the shift: `B(ι n, r) ↦ B(ι m, s)` is
listed with the witness `k` when `0 < r ≤ 2^{-k} < s` and `ι m` agrees with `σ(ι n)` below `k`. -/
def ShiftRel (z : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ) : Prop :=
  0 < z.1.1.2 ∧ 0 < z.1.2.2 ∧ ¬ (2 : ℚ)⁻¹ ^ z.2 < z.1.1.2 ∧ (2 : ℚ)⁻¹ ^ z.2 < z.1.2.2 ∧
    (List.range z.2).map (fun i ↦ (word z.1.2.1).getD i false) =
      (List.range z.2).map (fun i ↦ (word z.1.1.1).getD (i + 1) false)

/-- `ShiftRel` is decidable. -/
instance : DecidablePred ShiftRel := fun _ ↦ by unfold ShiftRel; infer_instance

/-- The kernel `ShiftRel` is decidable by a computable procedure. -/
lemma computable_decide_shiftRel : Computable fun z ↦ decide (ShiftRel z) := by
  have hlt : ∀ {f g : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ → ℚ}, Computable f → Computable g →
      Computable fun z ↦ decide (f z < g z) := fun hf hg ↦ computable₂_ratLt.comp hf hg
  have hr : Computable fun z : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ ↦ z.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hs : Computable fun z : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ ↦ z.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hp : Computable fun z : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ ↦ (2 : ℚ)⁻¹ ^ z.2 :=
    computable_inv_two_pow.comp Computable.snd
  have hmap : ∀ c : ℕ, Primrec₂ fun (w : List Bool) (k : ℕ) ↦
      (List.range k).map (fun i ↦ w.getD (i + c) false) :=
    fun c ↦ Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (primrec_getD.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_add.comp Primrec.snd (Primrec.const c))).to₂
  have hm : Computable fun z : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ ↦
      (List.range z.2).map (fun i ↦ (word z.1.2.1).getD (i + 0) false) :=
    (hmap 0).to_comp.comp (computable_word.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst))) Computable.snd
  have hn : Computable fun z : ((ℕ × ℚ) × (ℕ × ℚ)) × ℕ ↦
      (List.range z.2).map (fun i ↦ (word z.1.1.1).getD (i + 1) false) :=
    (hmap 1).to_comp.comp (computable_word.comp
      (Computable.fst.comp (Computable.fst.comp Computable.fst))) Computable.snd
  have heq := (primrec_decideEq.to_comp.comp hm hn)
  have h := Primrec.and.to_comp.comp (hlt (Computable.const 0) hr)
    (Primrec.and.to_comp.comp (hlt (Computable.const 0) hs)
      (Primrec.and.to_comp.comp (Primrec.not.to_comp.comp (hlt hp hr))
        (Primrec.and.to_comp.comp (hlt hp hs) heq)))
  refine h.of_eq fun z ↦ ?_
  simp only [ShiftRel, Bool.decide_and, decide_not, add_zero]

end CantorPres

/-- The shift is represented in `cantorPresentation`, relative to every oracle.
Blueprint node `meas:examples`. -/
theorem cantorPres_isRepresentedMapIn_shiftMap (A : Set ℕ) :
    IsRepresentedMapIn cantorPresentation cantorPresentation A shiftMap := by
  classical
  refine ⟨fun bc ↦ ∃ k, ShiftRel (bc, k),
    (isREIn_of_computable_decide computable_decide_shiftRel).exists, ?_, ?_⟩
  · rintro ⟨n, r⟩ ⟨m, s⟩ ⟨k, hr, hs, hrk, hks, hagree⟩
    dsimp only at hr hs hrk hks hagree
    refine ⟨hr, hs, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    change dist y (cantorPresentation.ι n) < (r : ℝ) at hy
    change dist (shiftMap y) (cantorPresentation.ι m) < (s : ℝ)
    have hrk' : (r : ℝ) ≤ (2 : ℝ)⁻¹ ^ k := by
      rw [← cast_inv_two_pow_real]; exact_mod_cast not_lt.mp hrk
    have hks' : (2 : ℝ)⁻¹ ^ k < (s : ℝ) := by rw [← cast_inv_two_pow_real]; exact_mod_cast hks
    have hyk := dist_lt_pow_iff.mp (hy.trans_le hrk')
    refine (dist_le_pow fun i hi ↦ ?_).trans_lt hks'
    have h1 := List.map_inj_left.mp hagree i (List.mem_range.mpr hi)
    simp only [shiftMap, hyk (i + 1) (by omega), cantorPres_ι, pad]
    exact h1.symm
  · rintro x ⟨m, s⟩ hx
    change dist (shiftMap x) (cantorPresentation.ι m) < (s : ℝ) at hx
    have hs : (0 : ℝ) < s := dist_nonneg.trans_lt hx
    have hex : ∃ k, (2 : ℝ)⁻¹ ^ k < s := exists_pow_lt_of_lt_one hs (by norm_num)
    set k := Nat.find hex with hk_def
    have hks : (2 : ℝ)⁻¹ ^ k < s := Nat.find_spec hex
    have hagree : ∀ i < k, shiftMap x i = cantorPresentation.ι m i := by
      intro i hi
      have hmin : ¬ (2 : ℝ)⁻¹ ^ (k - 1) < s := Nat.find_min hex (by omega)
      exact dist_lt_pow_iff.mp (hx.trans_le (not_lt.mp hmin)) i (by omega)
    refine ⟨(Encodable.encode (wordPrefix x (k + 1)), (2 : ℚ)⁻¹ ^ k),
      ⟨k, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · change (0 : ℚ) < (2 : ℚ)⁻¹ ^ k
      positivity
    · change (0 : ℚ) < s
      exact_mod_cast hs
    · exact lt_irrefl ((2 : ℚ)⁻¹ ^ k)
    · change (2 : ℚ)⁻¹ ^ k < s
      rw [← cast_inv_two_pow_real] at hks
      exact_mod_cast hks
    · refine List.map_congr_left fun i hi ↦ ?_
      have hi := List.mem_range.mp hi
      have h1 := hagree i hi
      simp only [shiftMap, cantorPres_ι, pad] at h1
      simp only [word_encode]
      rw [← h1]
      exact (pad_wordPrefix_of_lt x (by omega : i + 1 < k + 1)).symm
    · change dist x (cantorPresentation.ι _) < (((2 : ℚ)⁻¹ ^ k : ℚ) : ℝ)
      rw [cantorPres_ι_encode]
      push_cast
      calc dist x (pad (wordPrefix x (k + 1))) ≤ (2 : ℝ)⁻¹ ^ (k + 1) :=
            dist_le_pow fun i hi ↦ (pad_wordPrefix_of_lt x hi).symm
        _ < (2 : ℝ)⁻¹ ^ k := pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) k.lt_succ_self

namespace CantorPres

/-! ### Basic balls are unions of cylinders -/

/-- The certificate that the cylinder `[w]` lies in the basic ball `B(ι b.1, b.2)`:
`d(pad w, ι b.1) + 2^{-|w|} < b.2`. -/
def Cert (w : List Bool) (b : ℕ × ℚ) : Prop :=
  distQ w (word b.1) + (2 : ℚ)⁻¹ ^ w.length < b.2

/-- `Cert` is decidable. -/
instance (w : List Bool) (b : ℕ × ℚ) : Decidable (Cert w b) := by unfold Cert; infer_instance

/-- The certificate is decidable by a computable procedure. -/
lemma computable_decide_cert : Computable₂ fun w b ↦ decide (Cert w b) := by
  have h : Computable fun z : List Bool × (ℕ × ℚ) ↦
      decide (distQ z.1 (word z.2.1) + (2 : ℚ)⁻¹ ^ z.1.length < z.2.2) :=
    computable₂_ratLt.comp (computable₂_ratAdd.comp
      (computable_distQ.comp Computable.fst (computable_word.comp
        (Computable.fst.comp Computable.snd)))
      (computable_inv_two_pow.comp (Computable.list_length.comp Computable.fst)))
      (Computable.snd.comp Computable.snd)
  exact h.of_eq fun z ↦ rfl

end CantorPres

/-- Every basic ball of `cantorPresentation` is the union of the cylinders `[w]` with a
certificate `d(pad w, ι b.1) + 2^{-|w|} < b.2` (a decidable condition).
Blueprint node `meas:examples`. -/
theorem cantorPres_basicBall_eq (b : ℕ × ℚ) :
    basicBall cantorPresentation b = ⋃ w ∈ {w | Cert w b}, listCylinder w := by
  ext y
  simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
  change dist y (cantorPresentation.ι b.1) < (b.2 : ℝ) ↔ _
  rw [cantorPres_ι]
  constructor
  · intro hy
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos (sub_pos.mpr hy))
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨wordPrefix y N, ?_, mem_listCylinder_wordPrefix y N⟩
    have hlen : (wordPrefix y N).length = N := by simp [wordPrefix]
    have h1 : dist (pad (wordPrefix y N)) y ≤ (2 : ℝ)⁻¹ ^ N :=
      dist_le_pow fun i hi ↦ pad_wordPrefix_of_lt y hi
    have h2 := dist_triangle (pad (wordPrefix y N)) y (pad (word b.1))
    rw [dist_pad] at h2
    have hc : ((distQ (wordPrefix y N) (word b.1) + (2 : ℚ)⁻¹ ^ (wordPrefix y N).length : ℚ) :
        ℝ) < (b.2 : ℝ) := by
      push_cast
      rw [hlen]
      linarith
    exact_mod_cast hc
  · rintro ⟨w, hw, hy⟩
    have hw' : ((distQ w (word b.1) + (2 : ℚ)⁻¹ ^ w.length : ℚ) : ℝ) < (b.2 : ℝ) :=
      by exact_mod_cast hw
    push_cast at hw'
    have h1 := dist_triangle y (pad w) (pad (word b.1))
    rw [dist_pad] at h1
    linarith [dist_pad_le hy]

/-! ### C.e. open sets are c.e. unions of cylinders -/

/-- The cylinders are uniformly c.e. open in `cantorPresentation`, relative to every oracle.
Blueprint node `meas:examples`. -/
theorem cantorPres_isCeOpenFamilyIn_listCylinder (A : Set ℕ) :
    IsCeOpenFamilyIn cantorPresentation A (listCylinder : List Bool → Set (ℕ → Bool)) :=
  isCeOpenFamilyIn_listCylinder (β := 1 / 2) (by norm_num) (by norm_num)
    (fun _ _ ↦ cantorMetricSpace_dist_eq) cantorPresentation A
    (cantorPres_computablePresentationIn A) (cantorPres_computableIn_symbols A)

/-- An `A`-c.e. open family of `cantorPresentation` is an `A`-c.e. union of cylinders,
uniformly. Blueprint node `meas:examples`. -/
theorem cantorPres_exists_words_of_isCeOpenFamilyIn {ι : Type*} [Primcodable ι] {A : Set ℕ}
    {U : ι → Set (ℕ → Bool)} (hU : IsCeOpenFamilyIn cantorPresentation A U) :
    ∃ E : ι × List Bool → Prop, IsREIn A E ∧
      ∀ i, U i = ⋃ w ∈ {w | E (i, w)}, listCylinder w := by
  obtain ⟨E, hE, hUE⟩ := hU
  refine ⟨fun iw ↦ ∃ b, E (iw.1, b) ∧ Cert iw.2 b, ?_, fun i ↦ ?_⟩
  · refine IsREIn.exists (F := fun z : (ι × List Bool) × (ℕ × ℚ) ↦ E (z.1.1, z.2) ∧
      Cert z.1.2 z.2) (IsREIn.and ?_ (isREIn_of_computable_decide ?_))
    · exact hE.comp ((Computable.fst.comp Computable.fst).pair Computable.snd).computableIn
    · exact computable_decide_cert.comp (Computable.snd.comp Computable.fst) Computable.snd
  · rw [hUE i]
    ext y
    simp only [cantorPres_basicBall_eq, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨b, hb, w, hw, hy⟩
      exact ⟨w, ⟨b, hb, hw⟩, hy⟩
    · rintro ⟨w, ⟨b, hb, hw⟩, hy⟩
      exact ⟨b, hb, w, hw, hy⟩

/-! ### Randomness for the presentation and for cylinder tests -/

/-- For `cantorPresentation`, Martin-Löf randomness relative to `A` is randomness for cylinder
tests relative to `A`, for every measure. Blueprint node `meas:examples`. -/
theorem cantorPres_randomPoints_eq (A : Set ℕ) (μ : Measure (ℕ → Bool)) :
    randomPoints cantorPresentation A μ = wordRandomPoints A μ := by
  ext x
  constructor
  · exact mem_wordRandomPoints_of_mem_randomPoints (β := 1 / 2) (by norm_num) (by norm_num)
      (fun _ _ ↦ cantorMetricSpace_dist_eq) cantorPresentation A
      (cantorPres_computablePresentationIn A) (cantorPres_computableIn_symbols A) μ
  · intro hx U hU
    obtain ⟨E, hE, hUE⟩ := cantorPres_exists_words_of_isCeOpenFamilyIn hU.1
    exact hx U ⟨E, hE, hUE, hU.2⟩

/-- A word test relative to the empty oracle gives a uniformly computable enumeration of
cylinders. -/
private lemma exists_computable_enumeration {E : ℕ × List Bool → Prop} (hE : IsREIn ∅ E) :
    ∃ f : ℕ → ℕ → Option (List Bool), Computable₂ f ∧
      ∀ m w, E (m, w) ↔ ∃ i, f m i = some w := by
  obtain ⟨e, he, henum⟩ := (relative_enumeration ∅ E).mp hE
  have hA : Partrec (charOracle (∅ : Set ℕ)) := by
    have h : charOracle (∅ : Set ℕ) = ((fun _ ↦ 0 : ℕ → ℕ) : ℕ →. ℕ) := by
      funext n
      simp [charOracle]
    rw [h]
    exact Computable.const 0
  have hec : Computable e :=
    RecursiveIn.partrec_of_oracle (fun g hg ↦ by rw [Set.mem_singleton_iff.mp hg]; exact hA) he
  let g : ℕ × ℕ → ℕ × List Bool → Option (List Bool) := fun a p ↦
    if p.1 = a.1 then some p.2 else none
  have hg : Primrec₂ g :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp Primrec.fst)) (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.const none)
  refine ⟨fun m i ↦ (e i).bind (g (m, i)), ?_, fun m w ↦ ?_⟩
  · exact Computable.option_bind (hec.comp Computable.snd) hg.to_comp.to₂
  · rw [henum]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, by simp [ht, g]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      cases h : e t with
      | none => simp [h] at ht
      | some p =>
        simp only [h, Option.bind_some, g] at ht
        split_ifs at ht with hp
        cases ht
        rw [← hp]

/-- Martin-Löf randomness in the sense of `AlgorithmicRandomness` (computable cylinder
enumerations) implies randomness for cylinder tests relative to the empty oracle, for every
measure. Blueprint node `meas:examples`. -/
theorem cantorPres_mem_wordRandomPoints_of_isMartinLofRandom {μ : Measure (ℕ → Bool)}
    {w : ℕ → Bool} (hw : IsMartinLofRandom μ w) : w ∈ wordRandomPoints ∅ μ := by
  rintro V ⟨E, hE, hV, hμV⟩
  obtain ⟨f, hf, hfE⟩ := exists_computable_enumeration hE
  have htest : IsMartinLofTest μ V := by
    refine ⟨⟨f, hf, fun n ↦ ?_⟩, fun n ↦ ?_⟩
    · rw [hV n]
      ext y
      simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨v, hv, hy⟩
        obtain ⟨i, hi⟩ := (hfE n v).mp hv
        exact ⟨i, by rw [hi]; exact hy⟩
      · rintro ⟨i, hi⟩
        cases h : f n i with
        | none => simp [h] at hi
        | some v =>
          rw [h] at hi
          exact ⟨v, (hfE n v).mpr ⟨i, h⟩, hi⟩
    · refine (hμV n).trans_eq ?_
      rw [Kolmogorov.dyadicValue, Nat.cast_one, one_div, ENNReal.inv_pow]
  by_contra hcon
  refine hw V htest (mem_iInter.mpr fun m ↦ ?_)
  by_contra hm
  exact hcon ⟨m, hm⟩

/-! ### Admissibility from cylinder computability -/

namespace CantorPres

/-- Whether some ball of the list `L` has a certificate for the cylinder `[w]`. -/
def certB (L : List (ℕ × ℚ)) (w : List Bool) : Bool := L.any fun b ↦ decide (Cert w b)

/-- Whether a prefix of length `≤ N` of `v` is certified for a ball of `L` (`LN = (L, N)`). -/
def reachB (LN : List (ℕ × ℚ) × ℕ) (v : List Bool) : Bool :=
  (List.range (LN.2 + 1)).any fun j ↦ certB LN.1 (v.take j)

/-- The words of length `N` with a prefix certified for a ball of `L` (`LN = (L, N)`). -/
def reachWords (LN : List (ℕ × ℚ) × ℕ) : List (List Bool) :=
  (PoincareAux.boolWords LN.2).filter (reachB LN)

/-- `certB` is computable. -/
lemma computable_certB : Computable₂ certB :=
  computable_list_any Computable.fst
    (computable_decide_cert.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂

/-- `reachB` is computable. -/
lemma computable_reachB : Computable₂ reachB := by
  refine computable_list_any (f := fun z : (List (ℕ × ℚ) × ℕ) × List Bool ↦
    List.range (z.1.2 + 1)) (p := fun z j ↦ certB z.1.1 (z.2.take j)) ?_ ?_
  · exact (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))).to_comp
  · exact (computable_certB.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Primrec.list_take.to_comp.comp Computable.snd
        (Computable.snd.comp Computable.fst))).to₂

/-- `reachWords` is computable. -/
lemma computable_reachWords : Computable reachWords :=
  computable_list_filter (PoincareAux.primrec_boolWords.to_comp.comp Computable.snd)
    computable_reachB

/-- `certB` decides a certificate in the list. -/
lemma certB_iff (L : List (ℕ × ℚ)) (w : List Bool) : certB L w = true ↔ ∃ b ∈ L, Cert w b := by
  simp [certB]

/-- A sequence is in the reach set of `(L, N)` iff one of its prefixes of length `≤ N` is
certified. -/
lemma reachB_wordPrefix_iff (L : List (ℕ × ℚ)) (N : ℕ) (x : ℕ → Bool) :
    reachB (L, N) (wordPrefix x N) = true ↔ ∃ j ≤ N, ∃ b ∈ L, Cert (wordPrefix x j) b := by
  simp only [reachB, List.any_eq_true, List.mem_range, certB_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [PoincareAux.wordPrefix_take x (by omega : j ≤ N)] at h
    exact ⟨j, by omega, h⟩
  · rintro ⟨j, hj, h⟩
    refine ⟨j, by omega, ?_⟩
    rwa [PoincareAux.wordPrefix_take x hj]

/-- A finite union of basic balls is the increasing union over `N` of the sets of sequences
whose prefix of length `N` has a certified prefix. -/
lemma ballUnion_eq_iUnion (L : List (ℕ × ℚ)) :
    ballUnion cantorPresentation L =
      ⋃ N, {x | reachB (L, N) (wordPrefix x N) = true} := by
  ext x
  simp only [ballUnion, cantorPres_basicBall_eq, mem_iUnion, mem_ofPred_eq, exists_prop,
    reachB_wordPrefix_iff]
  constructor
  · rintro ⟨b, hb, w, hw, hx⟩
    rw [PoincareAux.mem_listCylinder_iff] at hx
    exact ⟨w.length, w.length, le_rfl, b, hb, by rwa [hx]⟩
  · rintro ⟨N, j, -, b, hb, hw⟩
    exact ⟨b, hb, wordPrefix x j, hw, mem_listCylinder_wordPrefix x j⟩

/-- The reach sets increase with `N`. -/
lemma monotone_reach (L : List (ℕ × ℚ)) :
    Monotone fun N ↦ {x : ℕ → Bool | reachB (L, N) (wordPrefix x N) = true} := by
  intro N N' hNN' x hx
  simp only [mem_ofPred_eq, reachB_wordPrefix_iff] at hx ⊢
  obtain ⟨j, hj, h⟩ := hx
  exact ⟨j, hj.trans hNN', h⟩

/-- The measure of a reach set is the finite sum of the measures of the reached cylinders. -/
lemma measure_reach_toReal (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    (LN : List (ℕ × ℚ) × ℕ) :
    (μ {x | reachB LN (wordPrefix x LN.2) = true}).toReal =
      ((reachWords LN).map fun v ↦ (μ (listCylinder v)).toReal).sum := by
  rw [PoincareAux.measure_setOf_wordPrefix μ (fun v ↦ reachB LN v = true) LN.2,
    PoincareAux.toReal_list_sum _ _ fun v ↦ measure_ne_top μ _]
  simp only [reachWords, Bool.decide_eq_true]

end CantorPres

/-- A finite measure with `A`-computable cylinder measures is `A`-computable for
`cantorPresentation`. Blueprint node `meas:examples`. -/
theorem cantorPres_isComputableMeasureIn {A : Set ℕ} (μ : Measure (ℕ → Bool))
    [IsFiniteMeasure μ] (hμ : IsComputableWordMeasureIn A μ) :
    IsComputableMeasureIn cantorPresentation A μ := by
  have hsum := SymbolicLower.isComputableRealFamilyIn_listSum hμ computable_reachWords 1
    (by norm_num)
  have hgt := birkhoff_computableIn_gt A _ hsum
  have hre : IsREIn A fun z : List (ℕ × ℚ) × ℚ ↦
      ∃ N, (z.2 : ℝ) < (μ {x | reachB (z.1, N) (wordPrefix x N) = true}).toReal := by
    refine IsREIn.exists (F := fun y : (List (ℕ × ℚ) × ℚ) × ℕ ↦
      (y.1.2 : ℝ) < (μ {x | reachB (y.1.1, y.2) (wordPrefix x y.2) = true}).toReal) ?_
    have h := hgt.comp (((Computable.fst.comp Computable.fst).pair Computable.snd).pair
      (Computable.snd.comp Computable.fst)).computableIn
    convert h using 2 with y
    rw [Rat.cast_one, one_mul, ← measure_reach_toReal μ (y.1.1, y.2)]
  have hiff : ∀ z : List (ℕ × ℚ) × ℚ, (z.2 : ℝ) < (μ (ballUnion cantorPresentation z.1)).toReal ↔
      ∃ N, (z.2 : ℝ) < (μ {x | reachB (z.1, N) (wordPrefix x N) = true}).toReal := by
    rintro ⟨L, q⟩
    dsimp only
    constructor
    · intro h
      rcases lt_or_ge (q : ℝ) 0 with hq | hq
      · exact ⟨0, hq.trans_le ENNReal.toReal_nonneg⟩
      · have h' : ENNReal.ofReal q < μ (ballUnion cantorPresentation L) :=
          (ENNReal.ofReal_lt_iff_lt_toReal hq (measure_ne_top μ _)).mpr h
        rw [ballUnion_eq_iUnion, (monotone_reach L).measure_iUnion] at h'
        obtain ⟨N, hN⟩ := lt_iSup_iff.mp h'
        exact ⟨N, (ENNReal.ofReal_lt_iff_lt_toReal hq (measure_ne_top μ _)).mp hN⟩
    · rintro ⟨N, hN⟩
      refine hN.trans_le (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_))
      rw [ballUnion_eq_iUnion]
      exact subset_iUnion (fun N ↦ {x : ℕ → Bool | reachB (L, N) (wordPrefix x N) = true}) N
  change IsREIn A fun z : List (ℕ × ℚ) × ℚ ↦
    (z.2 : ℝ) < (μ (ballUnion cantorPresentation z.1)).toReal
  convert hre using 2 with z
  exact hiff z

/-- **Admissibility from cylinder computability.** A finite measure with `A`-computable
cylinder measures is admissible for `(ℕ → Bool, d, σ, μ)` and `cantorPresentation` relative
to `A`. Blueprint node `meas:examples`. -/
theorem cantorPres_isMeasureAdmissible {A : Set ℕ} (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ]
    (hμ : IsComputableWordMeasureIn A μ) :
    IsMeasureAdmissible cantorPresentation shiftMap μ A :=
  ⟨cantorPres_computablePresentationIn A, cantorPres_isRepresentedMapIn_shiftMap A,
    cantorPres_isComputableMeasureIn μ hμ⟩

/-- For a probability measure, admissibility for `cantorPresentation` relative to `A` is
equivalent to `A`-computability of the cylinder measures. Blueprint node `meas:examples`. -/
theorem cantorPres_isMeasureAdmissible_iff {A : Set ℕ} (μ : Measure (ℕ → Bool))
    [IsProbabilityMeasure μ] :
    IsMeasureAdmissible cantorPresentation shiftMap μ A ↔ IsComputableWordMeasureIn A μ :=
  ⟨fun h ↦ isComputableWordMeasureIn_of_isComputableMeasureIn (β := 1 / 2) (by norm_num)
      (by norm_num) (fun _ _ ↦ cantorMetricSpace_dist_eq) cantorPresentation A
      (cantorPres_computablePresentationIn A) (cantorPres_computableIn_symbols A) μ h.2.2,
    cantorPres_isMeasureAdmissible μ⟩

/-! ### The fair-coin measure -/

/-- The fair-coin measure of a cylinder: `λ[w] = 2^{-|w|}`. -/
lemma cantorPres_uniformMeasure_listCylinder (w : List Bool) :
    uniformMeasure (listCylinder w) = (2 : ℝ≥0∞)⁻¹ ^ w.length :=
  cantorMass_uniformMeasure w

/-- The fair-coin measure has computable cylinder measures, relative to every oracle.
Blueprint node `meas:examples`. -/
theorem cantorPres_isComputableWordMeasureIn_uniformMeasure (A : Set ℕ) :
    IsComputableWordMeasureIn A uniformMeasure := by
  refine ⟨fun z ↦ (2 : ℚ)⁻¹ ^ z.1.length,
    (computable_inv_two_pow.comp (Computable.list_length.comp Computable.fst)).computableIn,
    fun w p ↦ ?_⟩
  dsimp only
  rw [cantorPres_uniformMeasure_listCylinder, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, cast_inv_two_pow_real, sub_self, abs_zero]
  positivity

/-! ### Causal maps given by computable word maps -/

/-- The cylinder of the prefix `x↾n` is the `PiNat` cylinder of `x` of length `n`. -/
lemma cantorPres_listCylinder_wordPrefix (x : ℕ → Bool) (n : ℕ) :
    listCylinder (wordPrefix x n) = PiNat.cylinder x n :=
  listCylinder_wordPrefix x n

/-- Two sequences have the same prefix of length `n` iff they agree below `n`. -/
lemma cantorPres_wordPrefix_eq_iff {x y : ℕ → Bool} {n : ℕ} :
    wordPrefix y n = wordPrefix x n ↔ y ∈ PiNat.cylinder x n := by
  rw [← cantorPres_listCylinder_wordPrefix, PoincareAux.mem_listCylinder_iff]
  simp [wordPrefix]

/-- The prefix of length `|w|` of the padded word `w 0^∞` is `w`. -/
lemma cantorPres_wordPrefix_pad (w : List Bool) : wordPrefix (pad w) w.length = w :=
  PoincareAux.mem_listCylinder_iff.mp (pad_mem_listCylinder w)

/-- The sequence map induced by a length-preserving monotone word map `F`:
`(seqMap F y) i = F(y↾(i+1))_i`. -/
def CantorPres.seqMap (F : List Bool → List Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun i ↦ (F (wordPrefix y (i + 1))).getD i false

/-- A length-preserving monotone word map `F` computes its sequence map on prefixes:
`(seqMap F y)↾n = F(y↾n)`. -/
theorem cantorPres_wordPrefix_seqMap {F : List Bool → List Bool}
    (hlen : ∀ w, (F w).length = w.length)
    (hmono : ∀ w k, k ≤ w.length → F (w.take k) = (F w).take k) (y : ℕ → Bool) (n : ℕ) :
    wordPrefix (CantorPres.seqMap F y) n = F (wordPrefix y n) := by
  have hl : (wordPrefix y n).length = n := by simp [wordPrefix]
  refine List.ext_getElem (by rw [hlen, hl]; simp [wordPrefix]) fun i hi hi' ↦ ?_
  have hin : i < n := by simpa [wordPrefix] using hi
  have htake : F (wordPrefix y (i + 1)) = (F (wordPrefix y n)).take (i + 1) := by
    rw [← PoincareAux.wordPrefix_take y (by omega : i + 1 ≤ n), hmono _ _ (by rw [hl]; omega)]
  have hlhs : (wordPrefix (CantorPres.seqMap F y) n)[i] = CantorPres.seqMap F y i := by
    simp [wordPrefix]
  rw [hlhs, CantorPres.seqMap, htake]
  simp [List.getElem?_eq_getElem hi']

variable {f : (ℕ → Bool) → ℕ → Bool} {F : List Bool → List Bool}

/-- A word map computing a causal map preserves lengths. -/
lemma cantorPres_length_wordMap (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n))
    (w : List Bool) : (F w).length = w.length := by
  rw [← cantorPres_wordPrefix_pad w, ← hF]
  simp [wordPrefix]

/-- A word map computing a causal map is monotone: `F(w↾k) = F(w)↾k`. -/
lemma cantorPres_take_wordMap (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n))
    (w : List Bool) {k : ℕ} (hk : k ≤ w.length) : F (w.take k) = (F w).take k := by
  calc F (w.take k) = F (wordPrefix (pad w) k) := by
        rw [← PoincareAux.wordPrefix_take _ hk, cantorPres_wordPrefix_pad]
    _ = (wordPrefix (f (pad w)) w.length).take k := by rw [← hF, PoincareAux.wordPrefix_take _ hk]
    _ = (F w).take k := by rw [hF, cantorPres_wordPrefix_pad]

/-- A map given on prefixes by a word map is causal, in the form used in `RandomNonAtom`. -/
theorem cantorPres_causal (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) :
    ∀ x y n, y ∈ PiNat.cylinder x n → f y ∈ PiNat.cylinder (f x) n := by
  intro x y n hy
  rw [← cantorPres_wordPrefix_eq_iff, hF, hF, cantorPres_wordPrefix_eq_iff.mpr hy]

/-- The preimage of a cylinder under a map given on prefixes by a word map `F`. -/
lemma cantorPres_preimage_listCylinder (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n))
    (w : List Bool) :
    f ⁻¹' listCylinder w = {y | F (wordPrefix y w.length) = w} := by
  ext y
  simp only [mem_preimage, PoincareAux.mem_listCylinder_iff, mem_ofPred_eq, hF]

/-- A map given on prefixes by a word map is measurable. -/
theorem cantorPres_measurable (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) :
    Measurable f := by
  refine measurable_pi_iff.mpr fun i ↦ measurable_to_countable' fun b ↦ ?_
  have h : (fun y ↦ f y i) ⁻¹' {b} =
      {y | pad (F (wordPrefix y (i + 1))) i = b} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    rw [← hF, pad_wordPrefix_of_lt _ (Nat.lt_succ_self i)]
  rw [h]
  exact PoincareAux.measurableSet_setOf_wordPrefix (fun v ↦ pad (F v) i = b) (i + 1)

/-- The cylinder measures of an image `λ ∘ f⁻¹`: `λ(f⁻¹[w])` is the sum of the `λ[v]` over the
words `v` of length `|w|` with `F v = w`. -/
theorem cantorPres_map_listCylinder (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n))
    (lam : Measure (ℕ → Bool)) (w : List Bool) :
    lam.map f (listCylinder w) =
      (((PoincareAux.boolWords w.length).filter fun v ↦ decide (F v = w)).map
        fun v ↦ lam (listCylinder v)).sum := by
  rw [Measure.map_apply (cantorPres_measurable hF) (PoincareAux.measurableSet_listCylinder w),
    cantorPres_preimage_listCylinder hF,
    PoincareAux.measure_setOf_wordPrefix lam (fun v ↦ F v = w) w.length]

/-- The `PiNat` cylinders of an image `λ ∘ f⁻¹` about an image point:
`λ(f⁻¹[f(x)↾n]) = λ{y | F(y↾n) = F(x↾n)}`. -/
theorem cantorPres_map_cylinder (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n))
    (lam : Measure (ℕ → Bool)) (x : ℕ → Bool) (n : ℕ) :
    lam.map f (PiNat.cylinder (f x) n) = lam {y | F (wordPrefix y n) = F (wordPrefix x n)} := by
  have hlen : (wordPrefix (f x) n).length = n := by simp [wordPrefix]
  rw [← cantorPres_listCylinder_wordPrefix, Measure.map_apply (cantorPres_measurable hF)
    (PoincareAux.measurableSet_listCylinder _), cantorPres_preimage_listCylinder hF, hlen, hF]

/-- **Transfer of cylinder computability.** If `f` is given on prefixes by a computable word
map `F` (`f(y)↾n = F(y↾n)`) and the finite measure `λ` has `A`-computable cylinder measures,
so has `λ ∘ f⁻¹`. Blueprint node `meas:examples`. -/
theorem cantorPres_isComputableWordMeasureIn_map {A : Set ℕ} (hFc : Computable F)
    (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) (lam : Measure (ℕ → Bool))
    [IsFiniteMeasure lam] (hlam : IsComputableWordMeasureIn A lam) :
    IsComputableWordMeasureIn A (lam.map f) := by
  have hL : Computable fun w : List Bool ↦
      (PoincareAux.boolWords w.length).filter fun v ↦ decide (F v = w) :=
    computable_list_filter (PoincareAux.primrec_boolWords.to_comp.comp Computable.list_length)
      (primrec_decideEq.to_comp.comp (hFc.comp Computable.snd) Computable.fst).to₂
  have h := SymbolicLower.isComputableRealFamilyIn_listSum hlam hL 1 (by norm_num)
  unfold IsComputableWordMeasureIn
  convert h using 2 with w
  rw [Rat.cast_one, one_mul, cantorPres_map_listCylinder hF,
    PoincareAux.toReal_list_sum _ _ fun v ↦ measure_ne_top lam _]

/-- **Transfer of randomness.** If `f` is given on prefixes by an `A`-computable word map `F`
(`f(y)↾n = F(y↾n)`), then `f` maps `λ`-random sequences (cylinder tests relative to `A`) to
`λ ∘ f⁻¹`-random sequences. Blueprint node `meas:examples`. -/
theorem cantorPres_map_mem_wordRandomPoints {A : Set ℕ} (hFc : ComputableIn {charOracle A} F)
    (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) (lam : Measure (ℕ → Bool))
    {y : ℕ → Bool} (hy : y ∈ wordRandomPoints A lam) :
    f y ∈ wordRandomPoints A (lam.map f) := by
  rintro V ⟨E, hE, hV, hμV⟩
  set V' : ℕ → Set (ℕ → Bool) := fun m ↦ ⋃ v ∈ {v | E (m, F v)}, listCylinder v with hV'_def
  have hpre : ∀ m, V' m = f ⁻¹' V m := by
    intro m
    ext z
    simp only [hV'_def, hV m, preimage_iUnion, cantorPres_preimage_listCylinder hF, mem_iUnion,
      mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨v, hv, hz⟩
      rw [PoincareAux.mem_listCylinder_iff] at hz
      refine ⟨F v, hv, ?_⟩
      rw [cantorPres_length_wordMap hF, hz]
    · rintro ⟨w, hw, hz⟩
      refine ⟨wordPrefix z w.length, by rwa [hz], mem_listCylinder_wordPrefix z _⟩
  have htest : IsWordTestIn A lam V' := by
    refine ⟨fun mv ↦ E (mv.1, F mv.2), hE.comp (ComputableIn.fst.pair
      (hFc.comp ComputableIn.snd)), fun m ↦ rfl, fun m ↦ ?_⟩
    rw [hpre m]
    exact (Measure.le_map_apply (cantorPres_measurable hF).aemeasurable _).trans (hμV m)
  obtain ⟨m, hm⟩ := hy V' htest
  exact ⟨m, fun h ↦ hm (by rw [hpre m]; exact h)⟩

/-! ### Summary for images of the fair-coin measure -/

/-- For a map `f` given on prefixes by a computable word map, the image `λ ∘ f⁻¹` of the
fair-coin measure is a probability measure admissible for `cantorPresentation` and the shift
relative to every oracle. Blueprint node `meas:examples`. -/
theorem cantorPres_isMeasureAdmissible_map_uniformMeasure (A : Set ℕ) (hFc : Computable F)
    (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) :
    IsMeasureAdmissible cantorPresentation shiftMap (uniformMeasure.map f) A :=
  cantorPres_isMeasureAdmissible _ (cantorPres_isComputableWordMeasureIn_map hFc hF _
    (cantorPres_isComputableWordMeasureIn_uniformMeasure A))

/-- For a map `f` given on prefixes by a computable word map, `f` maps every Martin-Löf random
sequence (for the fair-coin measure `λ`) to a point of `randomPoints cantorPresentation ∅ μ`,
`μ = λ ∘ f⁻¹`. Blueprint node `meas:examples`. -/
theorem cantorPres_map_mem_randomPoints_of_isMartinLofRandom (hFc : Computable F)
    (hF : ∀ y n, wordPrefix (f y) n = F (wordPrefix y n)) {y : ℕ → Bool}
    (hy : IsMartinLofRandom uniformMeasure y) :
    f y ∈ randomPoints cantorPresentation ∅ (uniformMeasure.map f) := by
  rw [cantorPres_randomPoints_eq]
  exact cantorPres_map_mem_wordRandomPoints hFc.computableIn hF _
    (cantorPres_mem_wordRandomPoints_of_isMartinLofRandom hy)

end Kolmogorov.PointToSet
