/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Countable.Defs
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Relative.Pullback
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Halves

/-!
# Splitting one coordinate off an infinite join

The countable van Lambalgen theorem reduces to the binary one by splitting the `i`-th coordinate
off: the infinite join `⊕ⱼ xⱼ` and the pair `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` are related by a computable
permutation of positions that carries `piJoinMeasure μ` to the joined product of the product of
the other measures with `μ i`, so one is random exactly when the other is. The oracle of the other
coordinates, reindexed (`cantorPiJoinSkip`), is Turing equivalent to the infinite join with the
`i`-th coordinate blanked (`cantorPiJoinExcept`), which in turn computes the coordinates below `i`
(`cantorPiJoinBelow`).

## Conventions

The measures `μ i` are probability measures, so that `Measure.infinitePi μ` is their product.
Randomness is `IsMartinLofRandomIn`, relative to an arbitrary oracle `A`. A permutation of
positions acts on sequences by precomposition, `w ↦ w ∘ π`, and on measures by `Measure.map` of
that map; its invariance (`isMartinLofRandomIn_map_precomp_iff`, blueprint node `vl:permute`) is
in `Relative/Pullback.lean`.

The permutation splitting off the `i`-th coordinate sends the even position `2m` to the position
`pair (skipIndex i a) b` of the infinite join, where `(a, b) = unpair m`, and the odd position
`2m + 1` to `pair i m`. Its inverse sends `pair i b` to `2b + 1` and `pair a b` with `a ≠ i` to
`2 · pair a' b`, where `a'` is `a` below `i` and `a - 1` above it.

## Main declarations

* `exists_cantorPiJoin_eq` (blueprint node `vl:pi-join`): every sequence is an infinite join.
* `isProbabilityMeasure_piJoinMeasure` (blueprint node `vl:pi-join-measure`): the countable product
  of probability measures is a probability measure.
* `isMartinLofRandomIn_cantorPiJoin_iff_split` (blueprint node `vl:pi-split`): `⊕ⱼ xⱼ` is random for
  `piJoinMeasure μ` exactly when `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` is random for the joined product.
* `isMartinLofRandomIn_oracleJoin_cantorPiJoinSkip_iff`,
  `charOracle_oracleJoin_cantorPiJoinBelow_le` (blueprint node `vl:pi-oracles`): the reindexed and
  the blanked oracles of the other coordinates give the same relative randomness, and the oracle
  of the earlier coordinates is reducible to them.

Used by `AlgorithmicRandomness/VanLambalgen/MainResults.lean`.
-/

namespace Kolmogorov

open MeasureTheory
open PointToSet (oracleJoin)
open scoped Computability

variable {A : Set ℕ} {μ : ℕ → Measure CantorSeq} {x : ℕ → CantorSeq}

/-! ### The infinite join and its measure -/

/-- Every sequence is an infinite join: of its columns `j ↦ (k ↦ z (pair j k))`.
Blueprint node `vl:pi-join`. -/
theorem exists_cantorPiJoin_eq (z : CantorSeq) : ∃ x, cantorPiJoin x = z :=
  ⟨fun j k => z (Nat.pair j k), funext fun n => by simp only [cantorPiJoin, Nat.pair_unpair]⟩

private lemma measurable_cantorPiJoin : Measurable cantorPiJoin :=
  Measurable.of_eval fun _ => (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- The countable product of probability measures, carried by the infinite join, is a probability
measure. Blueprint node `vl:pi-join-measure`. -/
instance isProbabilityMeasure_piJoinMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (piJoinMeasure μ) :=
  inferInstanceAs (IsProbabilityMeasure ((Measure.infinitePi μ).map cantorPiJoin))

/-! ### Index maps -/

/-- The inverse of `skipIndex i` on the indices other than `i`: `j ↦ j` below `i` and
`j ↦ j - 1` above it. -/
private def unskipIndex (i j : ℕ) : ℕ := if j < i then j else j - 1

private lemma skipIndex_ne (i j : ℕ) : skipIndex i j ≠ i := by
  unfold skipIndex
  split_ifs <;> omega

private lemma unskipIndex_skipIndex (i j : ℕ) : unskipIndex i (skipIndex i j) = j := by
  unfold skipIndex unskipIndex
  split_ifs <;> omega

private lemma skipIndex_unskipIndex {i j : ℕ} (h : j ≠ i) : skipIndex i (unskipIndex i j) = j := by
  unfold skipIndex unskipIndex
  split_ifs <;> omega

private lemma primrec_skipIndex (i : ℕ) : Primrec (skipIndex i) :=
  Primrec.ite (PrimrecRel.comp Primrec.nat_lt Primrec.id (Primrec.const i)) Primrec.id
    (Primrec.nat_add.comp Primrec.id (Primrec.const 1))

private lemma primrec_unskipIndex (i : ℕ) : Primrec (unskipIndex i) :=
  Primrec.ite (PrimrecRel.comp Primrec.nat_lt Primrec.id (Primrec.const i)) Primrec.id
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))

/-- The position map splitting off the `i`-th coordinate: the even position `2m` goes to the
position of bit `(unpair m).2` of the `(unpair m).1`-th coordinate other than `i`, the odd
position `2m + 1` to the position of bit `m` of the `i`-th coordinate. -/
private def splitIndex (i n : ℕ) : ℕ :=
  if n % 2 = 0 then Nat.pair (skipIndex i (Nat.unpair (n / 2)).1) (Nat.unpair (n / 2)).2
  else Nat.pair i (n / 2)

/-- The inverse of `splitIndex i`. -/
private def mergeIndex (i m : ℕ) : ℕ :=
  if (Nat.unpair m).1 = i then 2 * (Nat.unpair m).2 + 1
  else 2 * Nat.pair (unskipIndex i (Nat.unpair m).1) (Nat.unpair m).2

private lemma primrec_splitIndex (i : ℕ) : Primrec (splitIndex i) := by
  have hd : Primrec fun n : ℕ => n / 2 := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hu : Primrec fun n : ℕ => Nat.unpair (n / 2) := Primrec.unpair.comp hd
  exact (Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (Primrec₂.natPair.comp ((primrec_skipIndex i).comp (Primrec.fst.comp hu))
      (Primrec.snd.comp hu))
    (Primrec₂.natPair.comp (Primrec.const i) hd)).of_eq fun _ => rfl

private lemma primrec_mergeIndex (i : ℕ) : Primrec (mergeIndex i) := by
  have h1 : Primrec fun m : ℕ => (Nat.unpair m).1 := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec fun m : ℕ => (Nat.unpair m).2 := Primrec.snd.comp Primrec.unpair
  exact (Primrec.ite (PrimrecRel.comp Primrec.eq h1 (Primrec.const i))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) h2) (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp ((primrec_unskipIndex i).comp h1) h2))).of_eq fun _ => rfl

private lemma splitIndex_mergeIndex (i : ℕ) :
    Function.LeftInverse (splitIndex i) (mergeIndex i) := by
  intro m
  have hodd : ∀ a : ℕ, ¬ (2 * a + 1) % 2 = 0 := fun a => by omega
  have hodd' : ∀ a : ℕ, (2 * a + 1) / 2 = a := fun a => by omega
  have heven : ∀ a : ℕ, (2 * a) % 2 = 0 := fun a => by omega
  have heven' : ∀ a : ℕ, 2 * a / 2 = a := fun a => by omega
  by_cases h : (Nat.unpair m).1 = i
  · simp only [mergeIndex, splitIndex, h, hodd, hodd', ↓reduceIte]
    rw [← h, Nat.pair_unpair]
  · simp only [mergeIndex, splitIndex, h, heven, heven', ↓reduceIte, Nat.unpair_pair,
      skipIndex_unskipIndex h, Nat.pair_unpair]

/-- Reading `⊕ⱼ xⱼ` through `splitIndex i` gives `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ`. -/
private lemma cantorPiJoin_comp_splitIndex (x : ℕ → CantorSeq) (i : ℕ) :
    cantorPiJoin x ∘ splitIndex i = cantorJoin (cantorPiJoinSkip x i) (x i) := by
  funext n
  by_cases h : n % 2 = 0
  · simp only [Function.comp_apply, splitIndex, cantorJoin, cantorPiJoinSkip, cantorPiJoin, h,
      ↓reduceIte, Nat.unpair_pair]
  · simp only [Function.comp_apply, splitIndex, cantorJoin, cantorPiJoin, h, ↓reduceIte,
      Nat.unpair_pair]

/-! ### The split of the product measure -/

/-- Inserting a sequence as the `i`-th coordinate between the others, which are listed in the
order of `skipIndex i`. -/
private def insertCoord (i : ℕ) (p : (ℕ → CantorSeq) × CantorSeq) : ℕ → CantorSeq :=
  fun j => if j = i then p.2 else p.1 (unskipIndex i j)

private lemma measurable_insertCoord (i : ℕ) : Measurable (insertCoord i) := by
  refine Measurable.of_eval fun j => ?_
  by_cases h : j = i
  · simpa [insertCoord, h] using measurable_snd
  · simp only [insertCoord, h, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_fst

/-- The preimage of a box under `insertCoord i` is a box in the other coordinates times the
constraint on the `i`-th one. -/
private lemma preimage_insertCoord_pi (i : ℕ) (s : Finset ℕ) (t : ℕ → Set CantorSeq) :
    insertCoord i ⁻¹' Set.pi ↑s t =
      Set.pi ↑((s.erase i).image (unskipIndex i)) (fun j => t (skipIndex i j)) ×ˢ
        (if i ∈ s then t i else Set.univ) := by
  ext ⟨y, c⟩
  rw [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_pi]
  constructor
  · intro h
    refine ⟨fun j' hj' => ?_, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hj')
      have hji := Finset.ne_of_mem_erase hj
      have hy := h j (Finset.mem_coe.2 (Finset.mem_of_mem_erase hj))
      simp only [insertCoord, hji, ↓reduceIte] at hy
      rwa [skipIndex_unskipIndex hji]
    · by_cases hi : i ∈ s
      · simpa [insertCoord, hi] using h i (Finset.mem_coe.2 hi)
      · simp only [hi, ↓reduceIte, Set.mem_univ]
  · rintro ⟨h1, h2⟩ j hj
    by_cases hji : j = i
    · rw [hji]
      rw [hji] at hj
      simpa [insertCoord, Finset.mem_coe.1 hj] using h2
    · have hy := h1 (unskipIndex i j)
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hji, hj⟩)))
      simp only [insertCoord, hji, ↓reduceIte]
      rwa [skipIndex_unskipIndex hji] at hy

/-- The product measure is the product of the measures of the other coordinates and of the
`i`-th one, carried back by `insertCoord i`. -/
private lemma map_insertCoord_prod [∀ j, IsProbabilityMeasure (μ j)] (i : ℕ) :
    ((Measure.infinitePi fun j => μ (skipIndex i j)).prod (μ i)).map (insertCoord i) =
      Measure.infinitePi μ := by
  refine Measure.eq_infinitePi μ fun s t ht => ?_
  have hinj : Set.InjOn (unskipIndex i) ↑(s.erase i) := fun a ha b hb hab => by
    have ha' := Finset.ne_of_mem_erase (Finset.mem_coe.1 ha)
    have hb' := Finset.ne_of_mem_erase (Finset.mem_coe.1 hb)
    simp only [unskipIndex] at hab
    split_ifs at hab <;> omega
  have hprod : ∏ j ∈ s.erase i,
      μ (skipIndex i (unskipIndex i j)) (t (skipIndex i (unskipIndex i j))) =
        ∏ j ∈ s.erase i, μ j (t j) :=
    Finset.prod_congr rfl fun j hj => by rw [skipIndex_unskipIndex (Finset.ne_of_mem_erase hj)]
  rw [Measure.map_apply (measurable_insertCoord i)
      (MeasurableSet.pi s.countable_toSet fun j _ => ht j),
    preimage_insertCoord_pi, Measure.prod_prod, Measure.infinitePi_pi _ fun j _ => ht _,
    Finset.prod_image hinj, hprod]
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    exact Finset.prod_erase_mul s _ hi
  · simp only [hi, ↓reduceIte, measure_univ, mul_one, Finset.erase_eq_of_notMem hi]

/-- Reading the infinite join through `splitIndex i` carries `piJoinMeasure μ` to the joined
product of the product of the other measures with `μ i`. -/
private lemma piJoinMeasure_map_splitIndex [∀ j, IsProbabilityMeasure (μ j)] (i : ℕ) :
    (piJoinMeasure μ).map (fun w : CantorSeq => w ∘ splitIndex i) =
      joinMeasure (piJoinMeasure fun j => μ (skipIndex i j)) (μ i) := by
  have hprec : Measurable fun w : CantorSeq => w ∘ splitIndex i :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hprod := Measure.map_prod_map (Measure.infinitePi fun j => μ (skipIndex i j)) (μ i)
    measurable_cantorPiJoin measurable_id
  rw [Measure.map_id] at hprod
  rw [piJoinMeasure, piJoinMeasure, joinMeasure, ← map_insertCoord_prod i,
    Measure.map_map measurable_cantorPiJoin (measurable_insertCoord i),
    Measure.map_map hprec (measurable_cantorPiJoin.comp (measurable_insertCoord i)), hprod,
    Measure.map_map measurable_cantorJoin (measurable_cantorPiJoin.prodMap measurable_id)]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  rw [cantorPiJoin_comp_splitIndex]
  congr 1
  · simp only [cantorPiJoinSkip, insertCoord, skipIndex_ne, ↓reduceIte, unskipIndex_skipIndex]
  · simp [insertCoord]

/-- Splitting the `i`-th coordinate off: `⊕ⱼ xⱼ` is random for `piJoinMeasure μ` relative to `A`
exactly when `(⊕_{j ≠ i} xⱼ) ⊕ xᵢ` is random relative to `A` for the joined product of the
product of the other measures with `μ i`. Blueprint node `vl:pi-split`. -/
theorem isMartinLofRandomIn_cantorPiJoin_iff_split [∀ i, IsProbabilityMeasure (μ i)] (i : ℕ) :
    IsMartinLofRandomIn A (piJoinMeasure μ) (cantorPiJoin x) ↔
      IsMartinLofRandomIn A (joinMeasure (piJoinMeasure fun j => μ (skipIndex i j)) (μ i))
        (cantorJoin (cantorPiJoinSkip x i) (x i)) := by
  refine (isMartinLofRandomIn_map_precomp_iff (primrec_splitIndex i) (primrec_mergeIndex i)
    (splitIndex_mergeIndex i) (ν := piJoinMeasure μ) (z := cantorPiJoin x)).trans ?_
  rw [piJoinMeasure_map_splitIndex, cantorPiJoin_comp_splitIndex]

/-! ### The oracles of the other coordinates -/

/-- If every bit of `u` is either the constant `false` or a bit of `v`, at a primitive recursive
position and by a primitive recursive choice, then `A ⊕ u` is Turing reducible to `A ⊕ v`. -/
private lemma charOracle_oracleJoin_seqOracle_le {u v : CantorSeq} {c : ℕ → Bool} {f : ℕ → ℕ}
    (hc : Primrec c) (hf : Primrec f) (h : ∀ n, u n = (c n && v (f n))) :
    charOracle (oracleJoin A (seqOracle u)) ≤ᵀ charOracle (oracleJoin A (seqOracle v)) := by
  refine PointToSet.oracle_joins_least A _ _ (PointToSet.oracle_joins A _) ?_
  have hq : PartrecIn {charOracle (oracleJoin A (seqOracle v))}
      fun n => charOracle (oracleJoin A (seqOracle v)) (2 * f n + 1) :=
    PartrecIn.comp (PartrecIn.oracle _ (Set.mem_singleton _))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hf)
        (Primrec.const 1)).computableIn
  refine PartrecIn.of_eq (PartrecIn.cond_some hc.computableIn hq (ComputableIn.const 0))
    fun n => ?_
  have hodd : (2 * f n + 1) % 2 = 1 := by omega
  have hodd' : (2 * f n + 1) / 2 = f n := by omega
  cases hcn : c n
  · simp [charOracle, seqOracle, h n, hcn]
  · simp [charOracle, seqOracle, PointToSet.oracleJoin, h n, hcn, hodd, hodd']

/-- The reindexed and the blanked oracles of the coordinates other than the `i`-th are Turing
equivalent, so randomness relative to `A` joined with either is the same.
Blueprint node `vl:pi-oracles`. -/
theorem isMartinLofRandomIn_oracleJoin_cantorPiJoinSkip_iff {ν : Measure CantorSeq}
    {w : CantorSeq} (i : ℕ) :
    IsMartinLofRandomIn (oracleJoin A (seqOracle (cantorPiJoinSkip x i))) ν w ↔
      IsMartinLofRandomIn (oracleJoin A (seqOracle (cantorPiJoinExcept x i))) ν w := by
  have h1 : Primrec fun n : ℕ => (Nat.unpair n).1 := Primrec.fst.comp Primrec.unpair
  have h2 : Primrec fun n : ℕ => (Nat.unpair n).2 := Primrec.snd.comp Primrec.unpair
  constructor
  · refine fun h => h.mono_oracle (charOracle_oracleJoin_seqOracle_le
      (c := fun n => !decide ((Nat.unpair n).1 = i))
      (f := fun n => Nat.pair (unskipIndex i (Nat.unpair n).1) (Nat.unpair n).2)
      (Primrec.not.comp (Primrec.eq.decide.comp h1 (Primrec.const i)))
      (Primrec₂.natPair.comp ((primrec_unskipIndex i).comp h1) h2) fun n => ?_)
    by_cases ha : (Nat.unpair n).1 = i
    · simp [cantorPiJoinExcept, cantorPiJoin, ha]
    · simp [cantorPiJoinExcept, cantorPiJoinSkip, cantorPiJoin, ha, skipIndex_unskipIndex ha]
  · refine fun h => h.mono_oracle (charOracle_oracleJoin_seqOracle_le (c := fun _ => true)
      (f := fun n => Nat.pair (skipIndex i (Nat.unpair n).1) (Nat.unpair n).2)
      (Primrec.const true) (Primrec₂.natPair.comp ((primrec_skipIndex i).comp h1) h2)
      fun n => ?_)
    simp [cantorPiJoinExcept, cantorPiJoinSkip, cantorPiJoin, skipIndex_ne]

/-- The coordinates before the `i`-th are computable from the coordinates other than the `i`-th:
`A ⊕ (⊕_{j < i} xⱼ)` is Turing reducible to `A ⊕ (⊕_{j ≠ i} xⱼ)`.
Blueprint node `vl:pi-oracles`. -/
theorem charOracle_oracleJoin_cantorPiJoinBelow_le (i : ℕ) :
    charOracle (oracleJoin A (seqOracle (cantorPiJoinBelow x i))) ≤ᵀ
      charOracle (oracleJoin A (seqOracle (cantorPiJoinExcept x i))) := by
  refine charOracle_oracleJoin_seqOracle_le (c := fun n => decide ((Nat.unpair n).1 < i))
    (f := fun n => n)
    (Primrec.nat_lt.decide.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const i)) Primrec.id
    fun n => ?_
  by_cases ha : (Nat.unpair n).1 < i
  · simp [cantorPiJoinBelow, cantorPiJoinExcept, cantorPiJoin, ha, Nat.ne_of_lt ha]
  · simp [cantorPiJoinBelow, cantorPiJoin, ha]

end Kolmogorov
