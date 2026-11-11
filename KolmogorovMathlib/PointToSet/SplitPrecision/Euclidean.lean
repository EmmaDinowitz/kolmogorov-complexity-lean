/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.SplitPrecision.Point

/-!
# Euclidean space as a split-precision space

Euclidean space `ℝⁿ` is modelled as `Fin n → ℝ` with the sup metric of Mathlib's product
metric.  Its ideal points are the rational points `Fin n → ℚ`, enumerated through the
`Primcodable` instance on `Fin n → ℚ` (`ratPoint`, `ratPointIndex`); this gives the
presentation `euclidPresentation n`.

For every oracle `A` we provide the split-precision data of `KolmogorovMathlib.PointToSet.
SplitPrecision.Point`:

* `computablePresentationIn_euclid`: the metric table is computable, since the distance of two
  rational points is the rational `max_i |qᵢ - qᵢ'|` (`ratSupDist`);
* `euclidNets`: precision nets.  The canonical point of a ball `B(x, 2⁻ʳ)` is the dyadic
  truncation of `x` at scale `2⁻⁽ʳ⁺²⁾` (`dyadicTrunc`), and the candidates of a rational point
  `q` are the dyadic points obtained from the truncation of `q` by shifting each coordinate by
  one of the nine offsets `-4, …, 4` (`euclidCand`);
* `hasLinearGrowth_euclid`: `K_r(x) ≤ C (r + 1)`, because the code of the dyadic truncation is
  computed from the binary codes of `r` and of the `n` integer parts `⌊2 ^ (r + 2) xᵢ⌋`, each of
  which has `O(r)` bits (`truncDecode`).

Blueprint node `split:euclidean`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

/-! ### Rational points -/

/-- The rational point of `ℚⁿ` with index `k` (the origin when `k` is not a code), decoded with
the `Primcodable` instance of `Fin n → ℚ`. Blueprint node `split:euclidean`. -/
def ratPoint (n k : ℕ) : Fin n → ℚ :=
  (@Encodable.decode (Fin n → ℚ) Primcodable.toEncodable k).getD 0

/-- The index of a rational point of `ℚⁿ`. Blueprint node `split:euclidean`. -/
def ratPointIndex (n : ℕ) (q : Fin n → ℚ) : ℕ :=
  @Encodable.encode (Fin n → ℚ) Primcodable.toEncodable q

/-- Decoding inverts the indexing of rational points. -/
theorem ratPoint_ratPointIndex (n : ℕ) (q : Fin n → ℚ) : ratPoint n (ratPointIndex n q) = q := by
  simp [ratPoint, ratPointIndex, Encodable.encodek]

/-- Decoding rational points is primitive recursive. -/
theorem primrec_ratPoint (n : ℕ) : Primrec (ratPoint n) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

/-- Indexing rational points is primitive recursive. -/
theorem primrec_ratPointIndex (n : ℕ) : Primrec (ratPointIndex n) :=
  Primrec.encode

/-! ### The presentation -/

/-- The presentation of `ℝⁿ` (with the sup metric) by the rational points.
Blueprint node `split:euclidean`. -/
noncomputable def euclidPresentation (n : ℕ) : Presentation (Fin n → ℝ) where
  ι k := fun i => (ratPoint n k i : ℝ)
  dense := by
    refine Metric.denseRange_iff.mpr fun x ε hε => ?_
    have h : ∀ i : Fin n, ∃ q : ℚ, |x i - q| < ε := fun i => exists_rat_near (x i) hε
    choose q hq using h
    refine ⟨ratPointIndex n q, ?_⟩
    rw [ratPoint_ratPointIndex, dist_pi_lt_iff hε]
    intro i
    simpa [Real.dist_eq] using hq i
  complete := inferInstance

/-- The ideal points of the Euclidean presentation. -/
theorem euclidPresentation_ι (n k : ℕ) :
    (euclidPresentation n).ι k = fun i => (ratPoint n k i : ℝ) := rfl

/-! ### The rational metric table -/

/-- The sup distance of two rational points, as a rational number (zero when `n = 0`).
Blueprint node `split:euclidean`. -/
def ratSupDist (n : ℕ) (a b : Fin n → ℚ) : ℚ :=
  (List.ofFn fun i => |a i - b i|).foldr max 0

/-- The maximum of a list of rationals (with default `0`) is nonnegative. -/
theorem zero_le_foldr_max (l : List ℚ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_rfl
  | cons y l ih => exact ih.trans (le_max_right _ _)

/-- Every member of a list is at most the maximum of the list. -/
theorem le_foldr_max {l : List ℚ} {x : ℚ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

/-- The maximum of a list of rationals is zero or a member of the list. -/
theorem foldr_max_eq_zero_or_mem (l : List ℚ) : l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons y l ih =>
    rw [List.foldr_cons]
    rcases le_total y (l.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h0 | hmem
      · exact Or.inl h0
      · exact Or.inr (List.mem_cons_of_mem _ hmem)
    · rw [max_eq_left h]
      exact Or.inr List.mem_cons_self

/-- The rational sup distance is the distance of the corresponding real points. -/
theorem cast_ratSupDist (n : ℕ) (a b : Fin n → ℚ) :
    ((ratSupDist n a b : ℚ) : ℝ) = dist (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) := by
  apply le_antisymm
  · rcases foldr_max_eq_zero_or_mem (List.ofFn fun i => |a i - b i|) with h0 | hmem
    · rw [ratSupDist, h0]
      simp
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
      rw [ratSupDist, ← hi]
      refine le_trans (le_of_eq ?_) (dist_le_pi_dist (fun i => (a i : ℝ)) (fun i => (b i : ℝ)) i)
      rw [Real.dist_eq]
      push_cast
      rfl
  · have h0 : (0 : ℝ) ≤ ratSupDist n a b := by
      exact_mod_cast zero_le_foldr_max _
    rw [dist_pi_le_iff h0]
    intro i
    rw [Real.dist_eq, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_le]
    exact le_foldr_max (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- The rational sup distance is computable. -/
theorem computable_ratSupDist (n : ℕ) :
    Computable fun ab : (Fin n → ℚ) × (Fin n → ℚ) => ratSupDist n ab.1 ab.2 := by
  have habs : Computable fun q : ℚ => |q| := by
    have h := ComputableReals.primrec_ratMax.to_comp.comp Computable.id
      ComputableReals.computable_ratNeg
    exact h.of_eq fun q => (abs_eq_max_neg).symm
  have hcoord : ∀ i : Fin n,
      Computable fun ab : (Fin n → ℚ) × (Fin n → ℚ) => |ab.1 i - ab.2 i| := by
    intro i
    have h1 : Computable fun ab : (Fin n → ℚ) × (Fin n → ℚ) => ab.1 i :=
      Computable.fin_app.comp Computable.fst (Computable.const i)
    have h2 : Computable fun ab : (Fin n → ℚ) × (Fin n → ℚ) => ab.2 i :=
      Computable.fin_app.comp Computable.snd (Computable.const i)
    exact habs.comp (ComputableReals.computable_ratSub.comp h1 h2)
  have hlist := Computable.list_ofFn hcoord
  have hfold : Primrec fun l : List ℚ => l.foldr max 0 :=
    Primrec.list_foldr (f := id) (g := fun _ => (0 : ℚ)) (h := fun _ p => max p.1 p.2)
      Primrec.id (Primrec.const 0)
      (ComputableReals.primrec_ratMax.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
  exact (hfold.to_comp.comp hlist).of_eq fun _ => rfl

/-- The metric table of the Euclidean presentation is computable relative to every oracle: the
distance of two rational points is their rational sup distance.
Blueprint node `split:euclidean`. -/
theorem computablePresentationIn_euclid (n : ℕ) (A : Set ℕ) :
    ComputablePresentationIn (euclidPresentation n) A := by
  refine ⟨fun t => ratSupDist n (ratPoint n t.1.1) (ratPoint n t.1.2), ?_, ?_⟩
  · have h1 : Computable fun t : (ℕ × ℕ) × ℕ => (ratPoint n t.1.1, ratPoint n t.1.2) :=
      ((primrec_ratPoint n).comp (Primrec.fst.comp Primrec.fst)).to_comp.pair
        ((primrec_ratPoint n).comp (Primrec.snd.comp Primrec.fst)).to_comp
    exact (((computable_ratSupDist n).comp h1).of_eq fun _ => rfl).computableIn
  · intro ij p
    change |((ratSupDist n (ratPoint n ij.1) (ratPoint n ij.2) : ℚ) : ℝ) -
      dist (fun i => (ratPoint n ij.1 i : ℝ)) (fun i => (ratPoint n ij.2 i : ℝ))| < _
    rw [cast_ratSupDist, sub_self, abs_zero]
    positivity

/-! ### Dyadic rationals and integer parts -/

/-- The dyadic rational `z / 2 ^ k`. Blueprint node `split:euclidean`. -/
def dyadicRat (z : ℤ) (k : ℕ) : ℚ := (z : ℚ) / 2 ^ k

/-- The dyadic rationals are computable from the numerator and the exponent, by searching for
the rational `c` with `c.num * 2 ^ k = z * c.den`. -/
theorem computable_dyadicRat : Computable₂ dyadicRat := by
  have hver : Primrec fun w : (ℤ × ℕ) × ℚ =>
      decide (w.2.num * ((2 ^ w.1.2 : ℕ) : ℤ) = w.1.1 * (w.2.den : ℤ)) :=
    (PrimrecRel.comp Primrec.eq
      (ComputableReals.primrec_intMul.comp (ComputableReals.primrec_ratNum.comp Primrec.snd)
        (ComputableReals.primrec_natCastInt.comp
          (primrec_two_pow_aux.comp (Primrec.snd.comp Primrec.fst))))
      (ComputableReals.primrec_intMul.comp (Primrec.fst.comp Primrec.fst)
        (ComputableReals.primrec_natCastInt.comp
          (ComputableReals.primrec_ratDen.comp Primrec.snd)))).decide
  refine ComputableReals.computable_of_verifier (p := fun (zk : ℤ × ℕ) (c : ℚ) =>
    decide (c.num * ((2 ^ zk.2 : ℕ) : ℤ) = zk.1 * (c.den : ℤ))) hver.to_comp.to₂ fun zk c => ?_
  have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.pos.ne'
  have hpow : ((2 : ℚ) ^ zk.2) ≠ 0 := by positivity
  have key : c = dyadicRat zk.1 zk.2 ↔ (c.num : ℚ) * 2 ^ zk.2 = (zk.1 : ℚ) * c.den := by
    rw [dyadicRat, eq_div_iff hpow, ← mul_left_inj' hden, ← ComputableReals.rat_mul_den c]
    constructor <;> intro h <;> linarith
  rw [decide_eq_true_eq, key, ← Int.cast_inj (α := ℚ)]
  push_cast
  exact Iff.rfl

/-- The integer part `⌊2 ^ k * t⌋` of a scaled rational. Blueprint node `split:euclidean`. -/
def floorMulPow (k : ℕ) (t : ℚ) : ℤ := ⌊(2 : ℚ) ^ k * t⌋

/-- The scaled integer part is computable, by searching for the integer `m` with
`m * t.den ≤ 2 ^ k * t.num < (m + 1) * t.den`. -/
theorem computable_floorMulPow : Computable₂ floorMulPow := by
  have hnum : Primrec fun w : (ℕ × ℚ) × ℤ => ((2 ^ w.1.1 : ℕ) : ℤ) * w.1.2.num :=
    ComputableReals.primrec_intMul.comp
      (ComputableReals.primrec_natCastInt.comp
        (primrec_two_pow_aux.comp (Primrec.fst.comp Primrec.fst)))
      (ComputableReals.primrec_ratNum.comp (Primrec.snd.comp Primrec.fst))
  have hden : Primrec fun w : (ℕ × ℚ) × ℤ => (w.1.2.den : ℤ) :=
    ComputableReals.primrec_natCastInt.comp
      (ComputableReals.primrec_ratDen.comp (Primrec.snd.comp Primrec.fst))
  have h1 : Primrec fun w : (ℕ × ℚ) × ℤ =>
      decide (w.2 * (w.1.2.den : ℤ) ≤ ((2 ^ w.1.1 : ℕ) : ℤ) * w.1.2.num) :=
    (PrimrecRel.comp ComputableReals.primrec_intLe
      (ComputableReals.primrec_intMul.comp Primrec.snd hden) hnum).decide
  have h2 : Primrec fun w : (ℕ × ℚ) × ℤ =>
      decide (((2 ^ w.1.1 : ℕ) : ℤ) * w.1.2.num < (w.2 + 1) * (w.1.2.den : ℤ)) :=
    (PrimrecRel.comp ComputableReals.primrec_intLt hnum
      (ComputableReals.primrec_intMul.comp
        (ComputableReals.primrec_intAdd.comp Primrec.snd (Primrec.const 1)) hden)).decide
  have hver := Primrec.and.comp h1 h2
  refine ComputableReals.computable_of_verifier (p := fun (kt : ℕ × ℚ) (m : ℤ) =>
    (decide (m * (kt.2.den : ℤ) ≤ ((2 ^ kt.1 : ℕ) : ℤ) * kt.2.num) &&
      decide (((2 ^ kt.1 : ℕ) : ℤ) * kt.2.num < (m + 1) * (kt.2.den : ℤ))))
    hver.to_comp.to₂ fun kt m => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, floorMulPow, eq_comm,
    Int.floor_eq_iff]
  have hden : (0 : ℚ) < kt.2.den := by exact_mod_cast kt.2.pos
  have hmul : (2 : ℚ) ^ kt.1 * kt.2 = ((((2 ^ kt.1 : ℕ) : ℤ) * kt.2.num : ℤ) : ℚ) / kt.2.den := by
    push_cast
    rw [eq_div_iff hden.ne', mul_assoc, ComputableReals.rat_mul_den]
  rw [hmul, le_div_iff₀ hden, div_lt_iff₀ hden]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

/-- The dyadic rational `⌊2 ^ k * y⌋ / 2 ^ k` is within `2⁻ᵏ` of `y`. -/
theorem abs_dyadicRat_floor_sub_lt (k : ℕ) (y : ℝ) :
    |((dyadicRat ⌊(2 : ℝ) ^ k * y⌋ k : ℚ) : ℝ) - y| < (2 : ℝ)⁻¹ ^ k := by
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hfl := Int.floor_le ((2 : ℝ) ^ k * y)
  have hfl' := Int.lt_floor_add_one ((2 : ℝ) ^ k * y)
  have h1 : ((⌊(2 : ℝ) ^ k * y⌋ : ℤ) : ℝ) / 2 ^ k ≤ y := by
    rw [div_le_iff₀ hpos]
    linarith
  have h2 : y - (2 ^ k)⁻¹ < ((⌊(2 : ℝ) ^ k * y⌋ : ℤ) : ℝ) / 2 ^ k := by
    rw [lt_div_iff₀ hpos, sub_mul, inv_mul_cancel₀ hpos.ne']
    linarith
  rw [dyadicRat, inv_pow, abs_sub_lt_iff]
  push_cast
  constructor <;> linarith [inv_pos.mpr hpos]

/-! ### Dyadic truncations and candidates -/

/-- The coordinatewise dyadic truncation of a point of `ℝⁿ` at scale `2⁻ᵏ`.
Blueprint node `split:euclidean`. -/
noncomputable def dyadicTrunc (n k : ℕ) (x : Fin n → ℝ) : Fin n → ℚ :=
  fun i => dyadicRat ⌊(2 : ℝ) ^ k * x i⌋ k

/-- The dyadic truncation at scale `2⁻⁽ʳ⁺²⁾` lies in the ball `B(x, 2⁻ʳ)`. -/
theorem dist_dyadicTrunc_lt (n r : ℕ) (x : Fin n → ℝ) :
    dist (fun i => (dyadicTrunc n (r + 2) x i : ℝ)) x < dyadicRadius r := by
  rw [dist_pi_lt_iff (dyadicRadius_pos r)]
  intro i
  rw [Real.dist_eq]
  exact (abs_dyadicRat_floor_sub_lt (r + 2) (x i)).trans_le
    (dyadicRadius_antitone (by omega : r ≤ r + 2))

/-- The dyadic truncation, as an ideal point of the Euclidean presentation, lies in the ball. -/
theorem dist_euclid_dyadicTrunc_lt (n r : ℕ) (x : Fin n → ℝ) :
    dist ((euclidPresentation n).ι (ratPointIndex n (dyadicTrunc n (r + 2) x))) x <
      dyadicRadius r := by
  rw [euclidPresentation_ι, ratPoint_ratPointIndex]
  exact dist_dyadicTrunc_lt n r x

/-- The offset vector with index `j` (all offsets zero when `j` is not a code), decoded with the
`Primcodable` instance of `Fin n → Fin 9`. Blueprint node `split:euclidean`. -/
def offsetVec (n j : ℕ) : Fin n → Fin 9 :=
  (@Encodable.decode (Fin n → Fin 9) Primcodable.toEncodable j).getD 0

/-- The index of an offset vector. Blueprint node `split:euclidean`. -/
def offsetIndex (n : ℕ) (e : Fin n → Fin 9) : ℕ :=
  @Encodable.encode (Fin n → Fin 9) Primcodable.toEncodable e

/-- Decoding inverts the indexing of offset vectors. -/
theorem offsetVec_offsetIndex (n : ℕ) (e : Fin n → Fin 9) : offsetVec n (offsetIndex n e) = e := by
  simp [offsetVec, offsetIndex, Encodable.encodek]

/-- Decoding offset vectors is primitive recursive. -/
theorem primrec_offsetVec (n : ℕ) : Primrec (offsetVec n) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

/-- The `j`-th candidate of the rational point of index `q` at precision `r`: the dyadic point
at scale `2⁻⁽ʳ⁺²⁾` whose `i`-th numerator is `⌊2 ^ (r + 2) qᵢ⌋ + eᵢ - 4`, where `e` is the
offset vector of index `j`. Blueprint node `split:euclidean`. -/
def euclidCand (n r q j : ℕ) : ℕ :=
  ratPointIndex n fun i =>
    dyadicRat (floorMulPow (r + 2) (ratPoint n q i) + ((offsetVec n j i).val : ℤ) - 4) (r + 2)

/-- The candidate function is computable. -/
theorem computable_euclidCand (n : ℕ) :
    Computable fun t : ℕ × ℕ × ℕ => euclidCand n t.1 t.2.1 t.2.2 := by
  have hk : Primrec fun t : ℕ × ℕ × ℕ => t.1 + 2 :=
    Primrec.nat_add.comp Primrec.fst (Primrec.const 2)
  have hq : Primrec fun t : ℕ × ℕ × ℕ => ratPoint n t.2.1 :=
    (primrec_ratPoint n).comp (Primrec.fst.comp Primrec.snd)
  have he : Primrec fun t : ℕ × ℕ × ℕ => offsetVec n t.2.2 :=
    (primrec_offsetVec n).comp (Primrec.snd.comp Primrec.snd)
  have hcoord : ∀ i : Fin n, Computable fun t : ℕ × ℕ × ℕ =>
      dyadicRat (floorMulPow (t.1 + 2) (ratPoint n t.2.1 i) + ((offsetVec n t.2.2 i).val : ℤ) - 4)
        (t.1 + 2) := by
    intro i
    have hqi : Primrec fun t : ℕ × ℕ × ℕ => ratPoint n t.2.1 i :=
      Primrec.fin_app.comp hq (Primrec.const i)
    have hei : Primrec fun t : ℕ × ℕ × ℕ => ((offsetVec n t.2.2 i).val : ℤ) :=
      ComputableReals.primrec_natCastInt.comp
        (Primrec.fin_val.comp (Primrec.fin_app.comp he (Primrec.const i)))
    have hfl : Computable fun t : ℕ × ℕ × ℕ => floorMulPow (t.1 + 2) (ratPoint n t.2.1 i) :=
      computable_floorMulPow.comp hk.to_comp hqi.to_comp
    have hz : Computable fun t : ℕ × ℕ × ℕ =>
        floorMulPow (t.1 + 2) (ratPoint n t.2.1 i) + ((offsetVec n t.2.2 i).val : ℤ) - 4 := by
      have h := ComputableReals.primrec_intAdd.to_comp.comp
        (ComputableReals.primrec_intAdd.to_comp.comp hfl hei.to_comp) (Computable.const (-4 : ℤ))
      exact h.of_eq fun t => by ring
    exact computable_dyadicRat.comp hz hk.to_comp
  have hvec := Computable.vector_ofFn hcoord
  have hfun := Primrec.vector_get'.to_comp.comp hvec
  refine ((primrec_ratPointIndex n).to_comp.comp hfun).of_eq fun t => ?_
  exact congrArg (ratPointIndex n) (funext fun i => List.Vector.get_ofFn _ i)

/-- If `y` is within `2⁻ʳ` of `x`, the integer parts of `2 ^ (r + 2) x` and `2 ^ (r + 2) y`
differ by at most `4`. -/
theorem floor_sub_floor_bounds {r : ℕ} {x y : ℝ} (h : dist y x < dyadicRadius r) :
    0 ≤ ⌊(2 : ℝ) ^ (r + 2) * x⌋ - ⌊(2 : ℝ) ^ (r + 2) * y⌋ + 4 ∧
      ⌊(2 : ℝ) ^ (r + 2) * x⌋ - ⌊(2 : ℝ) ^ (r + 2) * y⌋ + 4 < 9 := by
  have hpow : (0 : ℝ) < 2 ^ r := by positivity
  rw [Real.dist_eq, dyadicRadius, inv_pow, abs_lt] at h
  have hu : 2 ^ r * (y - x) < 1 := by
    have := mul_lt_mul_of_pos_left h.2 hpow
    rwa [mul_inv_cancel₀ hpow.ne'] at this
  have hl : -1 < 2 ^ r * (y - x) := by
    have := mul_lt_mul_of_pos_left h.1 hpow
    rwa [mul_neg, mul_inv_cancel₀ hpow.ne'] at this
  have h4 : (2 : ℝ) ^ (r + 2) = 2 ^ r * 4 := by
    rw [pow_add]
    norm_num
  have hfx := Int.lt_floor_add_one ((2 : ℝ) ^ (r + 2) * x)
  have hfy := Int.lt_floor_add_one ((2 : ℝ) ^ (r + 2) * y)
  have hx := Int.floor_le ((2 : ℝ) ^ (r + 2) * x)
  have hy := Int.floor_le ((2 : ℝ) ^ (r + 2) * y)
  have hA : ⌊(2 : ℝ) ^ (r + 2) * y⌋ < ⌊(2 : ℝ) ^ (r + 2) * x⌋ + 5 := by
    rw [Int.floor_lt]
    push_cast
    rw [h4] at hfx ⊢
    linarith
  have hB : ⌊(2 : ℝ) ^ (r + 2) * x⌋ < ⌊(2 : ℝ) ^ (r + 2) * y⌋ + 5 := by
    rw [Int.floor_lt]
    push_cast
    rw [h4] at hfy ⊢
    linarith
  omega

/-- The scaled integer part of a rational is the integer part of the scaled real. -/
theorem floorMulPow_eq_floor_cast (k : ℕ) (t : ℚ) :
    floorMulPow k t = ⌊(2 : ℝ) ^ k * (t : ℝ)⌋ := by
  rw [floorMulPow, ← Rat.floor_cast (α := ℝ)]
  push_cast
  rfl

/-- **Precision nets of `ℝⁿ`**: the canonical point of `B(x, 2⁻ʳ)` is the dyadic truncation of
`x` at scale `2⁻⁽ʳ⁺²⁾`, which is a candidate of every rational point of the ball.
Blueprint node `split:euclidean`. -/
noncomputable def euclidNets (n : ℕ) (A : Set ℕ) : PrecisionNets (euclidPresentation n) A where
  cand := euclidCand n
  cand_computable := (computable_euclidCand n).computableIn
  bound := (Finset.univ.sup fun e : Fin n → Fin 9 => offsetIndex n e) + 1
  canonical := by
    intro r x
    refine ⟨ratPointIndex n (dyadicTrunc n (r + 2) x), dist_euclid_dyadicTrunc_lt n r x, ?_⟩
    intro q hq
    rw [euclidPresentation_ι, dist_pi_lt_iff (dyadicRadius_pos r)] at hq
    have hoff := fun i => floor_sub_floor_bounds (hq i)
    obtain ⟨e, he⟩ : ∃ e : Fin n → Fin 9, ∀ i, ((e i).val : ℤ) =
        ⌊(2 : ℝ) ^ (r + 2) * x i⌋ - ⌊(2 : ℝ) ^ (r + 2) * (ratPoint n q i : ℝ)⌋ + 4 :=
      ⟨fun i => ⟨(⌊(2 : ℝ) ^ (r + 2) * x i⌋ - ⌊(2 : ℝ) ^ (r + 2) * (ratPoint n q i : ℝ)⌋ +
        4).toNat, by have := hoff i; omega⟩, fun i => Int.toNat_of_nonneg (hoff i).1⟩
    refine ⟨offsetIndex n e, Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e)), ?_⟩
    unfold euclidCand
    rw [offsetVec_offsetIndex]
    refine congrArg (ratPointIndex n) (funext fun i => ?_)
    unfold dyadicTrunc
    refine congrArg (fun z => dyadicRat z (r + 2)) ?_
    rw [floorMulPow_eq_floor_cast, he i]
    ring

/-! ### Linear growth -/

/-- The code of an integer. -/
def intCode (m : ℤ) : ℕ := Encodable.encode m

/-- The integer with a given code (`0` for non-codes). -/
def intOfCode (k : ℕ) : ℤ := (Encodable.decode (α := ℤ) k).getD 0

/-- Decoding inverts the coding of integers. -/
theorem intOfCode_intCode (m : ℤ) : intOfCode (intCode m) = m := by
  rw [intOfCode, intCode, Encodable.encodek, Option.getD_some]

/-- Decoding integers is primitive recursive. -/
theorem primrec_intOfCode : Primrec intOfCode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const 0)

/-- The code of an integer is at most `2 |m| + 1`. -/
theorem intCode_le (m : ℤ) : intCode m ≤ 2 * m.natAbs + 1 := by
  rw [intCode, ← ComputableReals.encode_intEquivNatSumNat]
  cases m with
  | ofNat a =>
    change Encodable.encode (Sum.inl a : ℕ ⊕ ℕ) ≤ 2 * a + 1
    rw [Encodable.encode_inl, Encodable.encode_nat]
    omega
  | negSucc b =>
    change Encodable.encode (Sum.inr b : ℕ ⊕ ℕ) ≤ 2 * (b + 1) + 1
    rw [Encodable.encode_inr, Encodable.encode_nat]
    omega

/-- The integer part of `2 ^ k * y` has absolute value at most `2 ^ k (⌈|y|⌉₊ + 1)`. -/
theorem natAbs_floor_mul_pow_le (k : ℕ) (y : ℝ) :
    (⌊(2 : ℝ) ^ k * y⌋).natAbs ≤ 2 ^ k * (⌈|y|⌉₊ + 1) := by
  have hpow : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hfl := Int.floor_le ((2 : ℝ) ^ k * y)
  have hfl' := Int.lt_floor_add_one ((2 : ℝ) ^ k * y)
  have hceil := Nat.le_ceil |y|
  have habs := le_abs_self y
  have habs' := neg_abs_le y
  have hpos : (0 : ℝ) ≤ 2 ^ k := by positivity
  have hmul : (2 : ℝ) ^ k * y ≤ 2 ^ k * |y| := mul_le_mul_of_nonneg_left habs hpos
  have hmul' : (2 : ℝ) ^ k * (-|y|) ≤ 2 ^ k * y := mul_le_mul_of_nonneg_left habs' hpos
  have hmul'' : (2 : ℝ) ^ k * |y| ≤ 2 ^ k * ⌈|y|⌉₊ := mul_le_mul_of_nonneg_left hceil hpos
  have key : |((⌊(2 : ℝ) ^ k * y⌋ : ℤ) : ℝ)| ≤ ((2 ^ k * (⌈|y|⌉₊ + 1) : ℕ) : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> nlinarith
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] at key
  exact_mod_cast key

/-- The code of `⌊2 ^ k * y⌋` has at most `k + 1 + (Nat.bits (⌈|y|⌉₊ + 1)).length` bits. -/
theorem bits_length_intCode_floor_le (k : ℕ) (y : ℝ) :
    (Nat.bits (intCode ⌊(2 : ℝ) ^ k * y⌋)).length ≤
      k + 1 + (Nat.bits (⌈|y|⌉₊ + 1)).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le, pow_add, pow_succ]
  have h1 := intCode_le ⌊(2 : ℝ) ^ k * y⌋
  have h2 := natAbs_floor_mul_pow_le k y
  have h3 := Nat.lt_size_self (⌈|y|⌉₊ + 1)
  have h4 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  set M := ⌈|y|⌉₊ + 1
  set P := 2 ^ k
  set Q := 2 ^ M.size
  have h5 : 2 * (P * M) + 2 * P ≤ P * 2 * Q := by
    calc 2 * (P * M) + 2 * P = P * 2 * (M + 1) := by ring
      _ ≤ P * 2 * Q := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h3)
  omega

/-- Reconstruction of the code of a dyadic point from the binary codes of the precision `r`
(first entry) and of the integer parts of its coordinates (the next `n` entries): the output is
the binary code of `ratPointIndex n (fun i => dyadicRat mᵢ (r + 2))`.
Blueprint node `split:euclidean`. -/
def truncDecode (n : ℕ) (ws : List BitString) : BitString :=
  natBits (ratPointIndex n fun i : Fin n =>
    dyadicRat (intOfCode (decodeBits (ws.getD (i.val + 1) []))) (decodeBits (ws.getD 0 []) + 2))

/-- The reconstruction map is computable. -/
theorem computable_truncDecode (n : ℕ) : Computable (truncDecode n) := by
  have hgetD : Computable₂ fun (ws : List BitString) (m : ℕ) => ws.getD m [] :=
    (Primrec.list_getD ([] : BitString)).to_comp
  have hk : Computable fun ws : List BitString => decodeBits (ws.getD 0 []) + 2 :=
    Primrec.nat_add.to_comp.comp
      (decodeBits_computable.comp (hgetD.comp Computable.id (Computable.const 0)))
      (Computable.const 2)
  have hcoord : ∀ i : Fin n, Computable fun ws : List BitString =>
      dyadicRat (intOfCode (decodeBits (ws.getD (i.val + 1) [])))
        (decodeBits (ws.getD 0 []) + 2) := by
    intro i
    have hwi : Computable fun ws : List BitString => ws.getD (i.val + 1) [] :=
      hgetD.comp Computable.id (Computable.const (i.val + 1))
    exact computable_dyadicRat.comp
      (primrec_intOfCode.to_comp.comp (decodeBits_computable.comp hwi)) hk
  have hvec := Computable.vector_ofFn hcoord
  have hfun := Primrec.vector_get'.to_comp.comp hvec
  refine (natBits_computable.comp ((primrec_ratPointIndex n).to_comp.comp hfun)).of_eq
    fun ws => ?_
  exact congrArg natBits (congrArg (ratPointIndex n) (funext fun i => List.Vector.get_ofFn _ i))

/-- The `i`-th entry of `List.ofFn f` with a default. -/
theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The list of codes from which the dyadic truncation of `x` at precision `r` is
reconstructed. -/
noncomputable def truncCodes (n r : ℕ) (x : Fin n → ℝ) : List BitString :=
  natBits r :: List.ofFn fun i : Fin n => natBits (intCode ⌊(2 : ℝ) ^ (r + 2) * x i⌋)

/-- The reconstruction map recovers the code of the dyadic truncation. -/
theorem truncDecode_truncCodes (n r : ℕ) (x : Fin n → ℝ) :
    truncDecode n (truncCodes n r x) = natBits (ratPointIndex n (dyadicTrunc n (r + 2) x)) := by
  unfold truncDecode truncCodes dyadicTrunc
  refine congrArg natBits (congrArg (ratPointIndex n) (funext fun i => ?_))
  rw [List.getD_cons_succ, List.getD_cons_zero, getD_ofFn]
  simp only [natBits, decodeBits_natBits, intOfCode_intCode]

/-- The list of codes has `n + 1` entries. -/
theorem length_truncCodes (n r : ℕ) (x : Fin n → ℝ) : (truncCodes n r x).length = n + 1 := by
  simp [truncCodes]

/-- The sum of the complexities of the codes. -/
theorem sum_map_truncCodes (A : Set ℕ) (n r : ℕ) (x : Fin n → ℝ) :
    ((truncCodes n r x).map (oracleComplexity A)).sum = oracleNatComplexity A r +
      ∑ i : Fin n, oracleNatComplexity A (intCode ⌊(2 : ℝ) ^ (r + 2) * x i⌋) := by
  simp [truncCodes, List.map_ofFn, List.sum_ofFn, oracleNatComplexity]

/-- **Linear growth in `ℝⁿ`**: `K_r(x) ≤ C (r + 1)` for every oracle `A` and point `x`, with `C`
depending on `x`. Blueprint node `split:euclidean`. -/
theorem hasLinearGrowth_euclid (n : ℕ) (A : Set ℕ) (x : Fin n → ℝ) :
    HasLinearGrowth (euclidPresentation n) A x := by
  obtain ⟨c, hc⟩ := oracle_tuple_bounds_composition A (n + 1)
    (fun ws => Part.some (truncDecode n ws)) (computable_truncDecode n).computableIn.partrecIn
  obtain ⟨cB, hcB⟩ := oracleNatComplexity_le_bits A
  set S : ℕ := ∑ i : Fin n, (Nat.bits (⌈|x i|⌉₊ + 1)).length with hS
  refine ⟨3 + cB + c + n * (12 + cB) + 3 * S, fun r => ?_⟩
  have h1 : precisionComplexityNat (euclidPresentation n) A x (dyadicRadius r) ≤
      oracleNatComplexity A (ratPointIndex n (dyadicTrunc n (r + 2) x)) :=
    precisionComplexityNat_le_of_dist_lt' _ A x (dist_euclid_dyadicTrunc_lt n r x)
  have h2 := hc (truncCodes n r x) _ (length_truncCodes n r x) (Part.mem_some _)
  rw [truncDecode_truncCodes, sum_map_truncCodes] at h2
  have hr : oracleNatComplexity A r ≤ 3 * r + cB := by
    have := length_natBits_le r
    have := hcB r
    omega
  have hterm : ∀ i : Fin n, oracleNatComplexity A (intCode ⌊(2 : ℝ) ^ (r + 2) * x i⌋) ≤
      3 * (r + 3 + (Nat.bits (⌈|x i|⌉₊ + 1)).length) + cB := by
    intro i
    have := bits_length_intCode_floor_le (r + 2) (x i)
    have := hcB (intCode ⌊(2 : ℝ) ^ (r + 2) * x i⌋)
    omega
  have hsum : ∑ i : Fin n, oracleNatComplexity A (intCode ⌊(2 : ℝ) ^ (r + 2) * x i⌋) ≤
      n * (3 * (r + 3) + cB) + 3 * S := by
    calc ∑ i : Fin n, oracleNatComplexity A (intCode ⌊(2 : ℝ) ^ (r + 2) * x i⌋)
        ≤ ∑ i : Fin n, (3 * (r + 3 + (Nat.bits (⌈|x i|⌉₊ + 1)).length) + cB) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = n * (3 * (r + 3) + cB) + 3 * S := by
          rw [hS]
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul, Finset.mul_sum, mul_add]
          ring
  have h3 : oracleNatComplexity A (ratPointIndex n (dyadicTrunc n (r + 2) x)) ≤
      3 * r + cB + (n * (3 * (r + 3) + cB) + 3 * S) + c := by
    change oracleComplexity A (natBits _) ≤ _
    omega
  refine (h1.trans h3).trans ?_
  nlinarith [Nat.zero_le (n * r), Nat.zero_le (cB * r), Nat.zero_le (c * r),
    Nat.zero_le (S * r), Nat.zero_le (n * (cB * r))]

end Kolmogorov.PointToSet
