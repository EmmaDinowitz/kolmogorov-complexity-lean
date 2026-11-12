/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.Basic
import KolmogorovMathlib.AlgorithmicRandomness.Trim

/-!
# Trimming an oracle-uniform family uniformly in the oracle

Let `T z n` be an oracle-uniform family relative to `A` and `ν` a measure whose cylinder masses
have the approximations `a` (two-sided error `2^{-s}`, computable relative to `A`). This module
trims `T` uniformly in the oracle, at a trimming level `L`: at every oracle `z` the enumeration of
`T z n` is first disjointified (`disjEnum`) and then trimmed with the weights `a` (`trimEnum`,
`trimWeight` of `AlgorithmicRandomness/Trim.lean`). The result is again oracle-uniform relative
to `A` (`isOracleUniformIn_trimUniform`) and, for every oracle `z`,

* its member has `ν`-measure at most `2^{-L}` (`measure_uniformFamily_trimUniform_le`);
* it equals `T z n` unless `z` lies in the discard set (`uniformFamily_trimUniform_of_not_mem`),
  the set of oracles at which some interval is rejected;
* the discard set is uniformly effectively open relative to `A`
  (`isUniformlyEffectiveOpenIn_discardSet`) and contains only oracles with
  `ν (T z n) > 2^{-(L+2)}` (`lt_measure_of_mem_discardSet`).

The disjointified and trimmed enumerations at index `j` depend only on the first `j + 1` entries
of the enumeration of `T z n`, hence on the prefix of `z` of length `j`; the trimmed listing at a
finite oracle prefix `σ` is computed from finite lists and agrees with the one at every `z`
extending `σ`.

## Conventions

The trimmed family is listed by `trimUniform a g` at the level `Nat.pair n L`: `n` is the level
of the original family and `L` the trimming level. `trimUniform`, its finite-list helpers
(namespace `TrimUniform`) and `discardSet` are defined in `VanLambalgen/Auxiliary/Defs.lean`.
Measures are in `ℝ≥0∞`, the bound `2^{-L}` is `dyadicValue 1 L`, and `2^{-(L+2)}` is written
`(2 : ℝ≥0∞)⁻¹ ^ (L + 2)`, as in `Trim.lean`.

## Main declarations

* `isOracleUniformIn_trimUniform`, `measure_uniformFamily_trimUniform_le`,
  `uniformFamily_trimUniform_of_not_mem` (blueprint node `vl:uniform-trim`).
* `isUniformlyEffectiveOpenIn_discardSet`, `lt_measure_of_mem_discardSet`
  (blueprint node `vl:discard`): the oracles at which trimming discards something.

Used by the directions `vl:snd` and `vl:converse` in
`AlgorithmicRandomness/VanLambalgen/Directions/`.
-/

namespace Kolmogorov

open MeasureTheory ENNReal TrimUniform

variable {A : Set ℕ} {ν : Measure CantorSeq} {a : BitString → ℕ → ℕ}
  {g : BitString → ℕ → ℕ → Option BitString}

/-! ### Locality of disjointification and trimming -/

/-- The running maximum below `k` depends only on the values below `k`. -/
private theorem natMaxBelow_congr {len len' : ℕ → ℕ} {k : ℕ} (h : ∀ j < k, len j = len' j) :
    natMaxBelow len k = natMaxBelow len' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change max (natMaxBelow len k) (len k) = max (natMaxBelow len' k) (len' k)
    rw [ih fun j hj => h j (by omega), h k (by omega)]

/-- The count below `k` depends only on the values below `k`. -/
private theorem natCount_congr {c c' : ℕ → Bool} {k : ℕ} (h : ∀ j < k, c j = c' j) :
    natCount c k = natCount c' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change natCount c k + (bif c k then 1 else 0) = natCount c' k + (bif c' k then 1 else 0)
    rw [ih fun j hj => h j (by omega), h k (by omega)]

/-- The disjointified enumeration at index `i` depends only on the entries up to `i`. -/
private theorem disjEnum_congr {h h' : ℕ → Option BitString} {i : ℕ}
    (hh : ∀ j ≤ i, h j = h' j) : disjEnum h i = disjEnum h' i := by
  have hk : (Nat.unpair i).1 ≤ i := Nat.unpair_left_le i
  have hbit : ∀ u, disjBit h u (Nat.unpair i).1 = disjBit h' u (Nat.unpair i).1 := by
    intro u
    unfold disjBit maxLen coverCount
    rw [natMaxBelow_congr (len := lenOf h) (len' := lenOf h') (k := (Nat.unpair i).1 + 1)
        fun j hj => by simp only [lenOf, hh j (by omega)],
      natCount_congr (c := coverBit h u) (c' := coverBit h' u) (k := (Nat.unpair i).1)
        fun j hj => by simp only [coverBit, hh j (by omega)]]
    simp only [coverBit, hh _ hk]
  unfold disjEnum selEnum
  simp only [hbit]

/-- The trimming accumulator below `k` depends only on the weights below `k`. -/
private theorem trimPartial_congr {w w' : ℕ → ℕ} {k : ℕ} (h : ∀ j < k, w j = w' j) :
    trimPartial w k = trimPartial w' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (by omega)
    have ih' := ih fun j hj => h j (by omega)
    simp only [trimPartial_succ, trimAccept, ih', hk]

/-- The trimming decision at `k` depends only on the weights up to `k`. -/
private theorem trimAccept_congr {w w' : ℕ → ℕ} {k : ℕ} (h : ∀ j ≤ k, w j = w' j) :
    trimAccept w k = trimAccept w' k := by
  unfold trimAccept
  rw [trimPartial_congr (k := k) fun j hj => h j hj.le, h k le_rfl]

/-! ### The trimmed listing at a finite oracle prefix -/

/-- Below the length of the oracle prefix, `disjList` lists the disjointified enumeration at the
oracle. -/
private theorem listEnum_disjList (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq)
    (n : ℕ) {ℓ N k : ℕ} (hN : N ≤ ℓ + 1) (hk : k < N) :
    listEnum (disjList g (cantorPrefix z ℓ) n N) k = disjEnum (uniformEnum g z n) k := by
  have hlen : k < (disjList g (cantorPrefix z ℓ) n N).length := by simp [disjList, hk]
  rw [listEnum, List.getD_eq_getElem _ _ hlen]
  simp only [disjList, List.getElem_map, List.getElem_range]
  refine disjEnum_congr fun i hi => ?_
  -- below the prefix length, the prefix listing is the enumeration at the oracle
  have hiN : i < N := by omega
  have hiℓ : i ≤ ℓ := by omega
  unfold listEnum prefixEnumList
  rw [List.getD_eq_getElem _ _ (by simpa using hiN)]
  simp only [List.getElem_map, List.getElem_range, uniformEnum]
  rw [cantorPrefix_take _ _ _ ((Nat.unpair_left_le i).trans hiℓ)]

/-- At an index below the length of the oracle prefix, `localAccept` is the trimming decision
at the oracle. -/
private theorem localAccept_cantorPrefix (a : BitString → ℕ → ℕ)
    (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n L : ℕ) {ℓ j : ℕ}
    (hj : j ≤ ℓ) :
    localAccept a g (cantorPrefix z ℓ) n L j =
      trimAccept (trimWeight a (disjEnum (uniformEnum g z n)) L) j := by
  unfold localAccept
  refine trimAccept_congr fun k hk => ?_
  -- below the prefix length, the weight list holds the trimming weights at the oracle
  have hN : j + 1 ≤ ℓ + 1 := by omega
  have hkN : k < j + 1 := by omega
  rw [List.getD_eq_getElem _ _ (by simp [weightList, hkN])]
  simp only [weightList, List.getElem_map, List.getElem_range]
  unfold trimWeight
  rw [listEnum_disjList g z n hN hkN]

/-- At an index below the length of the oracle prefix, `localDisj` is the disjointified entry at
the oracle. -/
private theorem localDisj_cantorPrefix (g : BitString → ℕ → ℕ → Option BitString)
    (z : CantorSeq) (n : ℕ) {ℓ j : ℕ} (hj : j ≤ ℓ) :
    localDisj g (cantorPrefix z ℓ) n j = disjEnum (uniformEnum g z n) j :=
  listEnum_disjList g z n (by omega) (by omega)

/-- The local disjointified entry and trimming decision are computable relative to `A`, as
functions of `(σ, n, L, j)`. -/
private theorem computableIn_localData (ha : ComputableIn₂ {charOracle A} a)
    (hg : IsOracleUniformIn A g) :
    ComputableIn {charOracle A} fun x : BitString × ℕ × ℕ × ℕ =>
      (localDisj g x.1 x.2.1 x.2.2.2, localAccept a g x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hN : Primrec fun x : BitString × ℕ × ℕ × ℕ => x.2.2.2 + 1 :=
    Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)
  have hj : Primrec fun x : BitString × ℕ × ℕ × ℕ => x.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hPLf : ComputableIn₂ {charOracle A} fun (p : BitString × ℕ) (j : ℕ) =>
      g (p.1.take (Nat.unpair j).1) p.2 (Nat.unpair j).2 :=
    ComputableIn.of_eq (ComputableIn.comp hg ((Primrec.list_take.comp
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))).to_comp.computableIn)
      fun _ => rfl
  have hPL : ComputableIn {charOracle A} fun x : BitString × ℕ × ℕ × ℕ =>
      prefixEnumList g x.1 x.2.1 (x.2.2.2 + 1) :=
    ComputableIn.of_eq (ComputableIn.comp (computableIn_list_range_map hPLf)
      ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair hN).to_comp.computableIn)
      fun _ => rfl
  have hF : Computable₂ fun m i : ℕ =>
      ((Encodable.decode m : Option (List (Option BitString))).getD []).getD i none :=
    ((Primrec.list_getD none).comp (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst)
      (Primrec.const [])) Primrec.snd).to_comp
  have hΦ : Computable fun p : List (Option BitString) × ℕ => disjEnum (listEnum p.1) p.2 :=
    ((computable_disjEnum hF).comp (Computable.encode.comp Computable.fst)
      Computable.snd).of_eq fun p => by simp only [Encodable.encodek, Option.getD_some]; rfl
  have hDLf : ComputableIn₂ {charOracle A} fun (x : BitString × ℕ × ℕ × ℕ) (k : ℕ) =>
      disjEnum (listEnum (prefixEnumList g x.1 x.2.1 (x.2.2.2 + 1))) k :=
    ComputableIn.of_eq (ComputableIn.comp hΦ.computableIn
      ((ComputableIn.comp hPL ComputableIn.fst).pair ComputableIn.snd)) fun _ => rfl
  have hDL : ComputableIn {charOracle A} fun x : BitString × ℕ × ℕ × ℕ =>
      disjList g x.1 x.2.1 (x.2.2.2 + 1) :=
    ComputableIn.of_eq (ComputableIn.comp (computableIn_list_range_map hDLf)
      (ComputableIn.id.pair hN.to_comp.computableIn)) fun _ => rfl
  have hget : Computable fun p : List (Option BitString) × ℕ => p.1.getD p.2 none :=
    (Primrec.list_getD none).to_comp
  have he : ComputableIn {charOracle A} fun q : (BitString × ℕ × ℕ × ℕ) × ℕ =>
      listEnum (disjList g q.1.1 q.1.2.1 (q.1.2.2.2 + 1)) q.2 :=
    ComputableIn.of_eq (ComputableIn.comp hget.computableIn
      ((ComputableIn.comp hDL ComputableIn.fst).pair ComputableIn.snd)) fun _ => rfl
  have hw : ComputableIn₂ {charOracle A} fun (x : BitString × ℕ × ℕ × ℕ) (k : ℕ) =>
      trimWeight a (listEnum (disjList g x.1 x.2.1 (x.2.2.2 + 1))) x.2.2.1 k := by
    have hsome := ComputableIn.comp Primrec.option_isSome.to_comp.computableIn he
    have hgetD : Computable fun o : Option BitString => o.getD [] :=
      (Primrec.option_getD.comp Primrec.id (Primrec.const [])).to_comp
    have hprec : Computable fun q : (BitString × ℕ × ℕ × ℕ) × ℕ => q.1.2.2.1 + q.2 + 3 :=
      (Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
        (Primrec.const 3)).to_comp
    have hval := ComputableIn₂.comp ha (ComputableIn.comp hgetD.computableIn he)
      hprec.computableIn
    refine (PointToSet.computable_in_cond hsome hval (ComputableIn.const 0)).of_eq fun q => ?_
    unfold trimWeight
    dsimp only
    cases listEnum (disjList g q.1.1 q.1.2.1 (q.1.2.2.2 + 1)) q.2 <;> rfl
  have hWL : ComputableIn {charOracle A} fun x : BitString × ℕ × ℕ × ℕ =>
      weightList a g x.1 x.2.1 x.2.2.1 (x.2.2.2 + 1) :=
    ComputableIn.of_eq (ComputableIn.comp (computableIn_list_range_map hw)
      (ComputableIn.id.pair hN.to_comp.computableIn)) fun _ => rfl
  have hW : Computable₂ fun m k : ℕ =>
      ((Encodable.decode m : Option (List ℕ)).getD []).getD k 0 :=
    ((Primrec.list_getD 0).comp (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst)
      (Primrec.const [])) Primrec.snd).to_comp
  have hΨ : Computable fun p : List ℕ × ℕ => trimAccept (fun k => p.1.getD k 0) p.2 :=
    ((computable_trimAccept hW).comp (Computable.encode.comp Computable.fst)
      Computable.snd).of_eq fun p => by simp
  have hacc := ComputableIn.comp hΨ.computableIn (hWL.pair hj.to_comp.computableIn)
  have hdisj := ComputableIn.comp hget.computableIn (hDL.pair hj.to_comp.computableIn)
  exact (hdisj.pair hacc).of_eq fun _ => rfl

/-! ### The trimmed family -/

/-- The trimmed listing is oracle-uniform relative to `A`.
Blueprint node `vl:uniform-trim`. -/
theorem isOracleUniformIn_trimUniform (ha : ComputableIn₂ {charOracle A} a)
    (hg : IsOracleUniformIn A g) : IsOracleUniformIn A (trimUniform a g) := by
  have hx : Primrec fun p : BitString × ℕ × ℕ =>
      (p.1, (Nat.unpair p.2.1).1, (Nat.unpair p.2.1).2, p.2.2) :=
    Primrec.fst.pair ((Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))).pair
      ((Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))).pair
        (Primrec.snd.comp Primrec.snd)))
  have hd := ComputableIn.comp (computableIn_localData ha hg) hx.to_comp.computableIn
  have hH : Computable fun q : (BitString × ℕ × ℕ) × (Option BitString × Bool) =>
      bif decide (q.1.2.2 ≤ q.1.1.length) && q.2.2 then q.2.1 else none :=
    Computable.cond (Primrec.and.comp (Primrec.nat_le.decide.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.snd)).to_comp
      (Computable.fst.comp Computable.snd) (Computable.const none)
  exact (ComputableIn.comp hH.computableIn (ComputableIn.id.pair hd)).of_eq fun _ => rfl

/-- At the prefix of `z` of length `k` and an index `j ≤ k`, the trimmed listing is the trimmed
disjointified enumeration at `z`. -/
private theorem uniformEnum_trimUniform (a : BitString → ℕ → ℕ)
    (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n L : ℕ) {k j : ℕ}
    (hj : j ≤ k) :
    uniformEnum (trimUniform a g) z (Nat.pair n L) (Nat.pair k j) =
      trimEnum (disjEnum (uniformEnum g z n)) (trimWeight a (disjEnum (uniformEnum g z n)) L)
        j := by
  simp only [uniformEnum, trimUniform, Nat.unpair_pair, cantorPrefix_length, decide_eq_true hj,
    Bool.true_and, localAccept_cantorPrefix a g z n L hj, localDisj_cantorPrefix g z n hj,
    trimEnum]

/-- At an index above the length of the oracle prefix, the trimmed listing lists nothing. -/
private theorem uniformEnum_trimUniform_of_lt (a : BitString → ℕ → ℕ)
    (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n L : ℕ) {k j : ℕ}
    (hj : k < j) : uniformEnum (trimUniform a g) z (Nat.pair n L) (Nat.pair k j) = none := by
  simp [uniformEnum, trimUniform, Nat.not_le.2 hj]

/-- The trimmed family at `z` is the union of the trimmed disjointified enumeration at `z`. -/
private theorem uniformFamily_trimUniform (a : BitString → ℕ → ℕ)
    (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n L : ℕ) :
    uniformFamily (trimUniform a g) z (Nat.pair n L) =
      ⋃ j, coverSet (trimEnum (disjEnum (uniformEnum g z n))
        (trimWeight a (disjEnum (uniformEnum g z n)) L)) j := by
  ext y
  simp only [uniformFamily, Set.mem_iUnion]
  constructor
  · rintro ⟨j', hj'⟩
    obtain ⟨k, j, rfl⟩ : ∃ k j, j' = Nat.pair k j := ⟨_, _, (Nat.pair_unpair j').symm⟩
    rcases le_or_gt j k with hjk | hjk
    · exact ⟨j, by rwa [coverSet, uniformEnum_trimUniform a g z n L hjk] at hj'⟩
    · simp [coverSet, uniformEnum_trimUniform_of_lt a g z n L hjk] at hj'
  · rintro ⟨j, hj⟩
    exact ⟨Nat.pair j j, by rwa [coverSet, uniformEnum_trimUniform a g z n L le_rfl]⟩

/-- At every oracle, the trimmed family at the trimming
level `L` has `ν`-measure at most `2^{-L}`. Blueprint node `vl:uniform-trim`. -/
theorem measure_uniformFamily_trimUniform_le
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass ν x + dyadicValue 1 s ∧
      cantorMass ν x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n L : ℕ) :
    ν (uniformFamily (trimUniform a g) z (Nat.pair n L)) ≤ dyadicValue 1 L := by
  rw [uniformFamily_trimUniform]
  exact measure_iUnion_trimEnum_le ha _ L

/-! ### The discard set -/

/-- At an oracle outside the discard set, the
trimmed family is the original family. Blueprint node `vl:uniform-trim`. -/
theorem uniformFamily_trimUniform_of_not_mem {z : CantorSeq} {n L : ℕ}
    (hz : z ∉ discardSet a g n L) :
    uniformFamily (trimUniform a g) z (Nat.pair n L) = uniformFamily g z n := by
  simp only [discardSet, Set.mem_ofPred_eq, not_exists, not_and] at hz
  have key : ∀ j, trimEnum (disjEnum (uniformEnum g z n))
      (trimWeight a (disjEnum (uniformEnum g z n)) L) j = disjEnum (uniformEnum g z n) j := by
    intro j
    unfold trimEnum
    cases hacc : trimAccept (trimWeight a (disjEnum (uniformEnum g z n)) L) j with
    | true => rfl
    | false =>
      by_cases hD : disjEnum (uniformEnum g z n) j = none
      · rw [hD, Bool.cond_false]
      · exact absurd hacc (hz j hD)
  rw [uniformFamily_trimUniform, uniformFamily, ← coverSet_disjEnum_iUnion (uniformEnum g z n)]
  simp only [coverSet, key]

/-- An oracle in the discard set carries a member of measure more
than `2^{-(L+2)}`. Blueprint node `vl:discard`. -/
theorem lt_measure_of_mem_discardSet
    (ha : ∀ x s, dyadicValue (a x s) s ≤ cantorMass ν x + dyadicValue 1 s ∧
      cantorMass ν x ≤ dyadicValue (a x s) s + dyadicValue 1 s)
    {z : CantorSeq} {n L : ℕ} (hz : z ∈ discardSet a g n L) :
    (2 : ℝ≥0∞)⁻¹ ^ (L + 2) < ν (uniformFamily g z n) := by
  by_contra hle
  push Not at hle
  obtain ⟨j, hD, hacc⟩ := hz
  have hsmall : (∑' i, (disjEnum (uniformEnum g z n) i).elim 0 (cantorMass ν)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ (L + 2) := by
    rw [tsum_measure_disjEnum]
    exact hle
  have hself := trimEnum_eq_self_of_tsum_le ha hsmall j
  unfold trimEnum at hself
  rw [hacc, Bool.cond_false] at hself
  exact hD hself.symm

/-- The pair `(σ, j)` coded by a stage of the enumeration of the discard set. -/
private def discardStage (s : ℕ) : BitString × ℕ := (Encodable.decode s).getD ([], 0)

/-- The cylinder listed at stage `s` for the discard set at the level `m = Nat.pair n L`: the
string `σ` when the local data at `σ` show a rejected nonempty entry at an index `j ≤ |σ|`. -/
private def discardEnum (a : BitString → ℕ → ℕ) (g : BitString → ℕ → ℕ → Option BitString)
    (m s : ℕ) : Option BitString :=
  bif decide ((discardStage s).2 ≤ (discardStage s).1.length) &&
      (localDisj g (discardStage s).1 (Nat.unpair m).1 (discardStage s).2).isSome &&
      !localAccept a g (discardStage s).1 (Nat.unpair m).1 (Nat.unpair m).2 (discardStage s).2
    then some (discardStage s).1 else none

/-- The listing of the discard sets is computable relative to `A`. -/
private theorem computableIn_discardEnum (ha : ComputableIn₂ {charOracle A} a)
    (hg : IsOracleUniformIn A g) : ComputableIn₂ {charOracle A} (discardEnum a g) := by
  have hst : Primrec fun p : ℕ × ℕ => discardStage p.2 :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const _)).comp Primrec.snd
  have hx : Primrec fun p : ℕ × ℕ =>
      ((discardStage p.2).1, (Nat.unpair p.1).1, (Nat.unpair p.1).2, (discardStage p.2).2) :=
    (Primrec.fst.comp hst).pair ((Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)).pair (Primrec.snd.comp hst)))
  have hd := ComputableIn.comp (computableIn_localData ha hg) hx.to_comp.computableIn
  have hst' : Primrec fun q : (ℕ × ℕ) × (Option BitString × Bool) => discardStage q.1.2 :=
    hst.comp Primrec.fst
  have hH : Computable fun q : (ℕ × ℕ) × (Option BitString × Bool) =>
      bif decide ((discardStage q.1.2).2 ≤ (discardStage q.1.2).1.length) && q.2.1.isSome &&
        !q.2.2 then some (discardStage q.1.2).1 else none :=
    Computable.cond (Primrec.and.comp (Primrec.and.comp (Primrec.nat_le.decide.comp
        (Primrec.snd.comp hst') (Primrec.list_length.comp (Primrec.fst.comp hst')))
        (Primrec.option_isSome.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to_comp
      (Primrec.option_some.comp (Primrec.fst.comp hst')).to_comp (Computable.const none)
  exact (ComputableIn.comp hH.computableIn (ComputableIn.id.pair hd)).of_eq fun _ => rfl

/-- The discard sets, indexed by `Nat.pair n L`, form a
uniformly effectively open family relative to `A`. Blueprint node `vl:discard`. -/
theorem isUniformlyEffectiveOpenIn_discardSet (ha : ComputableIn₂ {charOracle A} a)
    (hg : IsOracleUniformIn A g) :
    IsUniformlyEffectiveOpenIn A fun m => discardSet a g (Nat.unpair m).1 (Nat.unpair m).2 := by
  refine ⟨discardEnum a g, computableIn_discardEnum ha hg, fun m => ?_⟩
  ext z
  simp only [discardSet, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hD, hacc⟩
    refine ⟨Encodable.encode (cantorPrefix z j, j), ?_⟩
    have hs : discardStage (Encodable.encode (cantorPrefix z j, j)) = (cantorPrefix z j, j) := by
      simp [discardStage, Encodable.encodek]
    have hsome : (disjEnum (uniformEnum g z (Nat.unpair m).1) j).isSome = true :=
      Option.isSome_iff_ne_none.2 hD
    have hc : (decide (j ≤ (cantorPrefix z j).length) &&
        (localDisj g (cantorPrefix z j) (Nat.unpair m).1 j).isSome &&
        !localAccept a g (cantorPrefix z j) (Nat.unpair m).1 (Nat.unpair m).2 j) = true := by
      rw [localDisj_cantorPrefix g z _ (le_refl j), localAccept_cantorPrefix a g z _ _ (le_refl j),
        hsome, hacc]
      simp
    simp only [discardEnum, hs, hc, Bool.cond_true, Option.elim_some]
    exact (isCantorPrefix_iff_cantorPrefix_eq _ _).2 (by simp)
  · rintro ⟨s, hs⟩
    unfold discardEnum at hs
    generalize discardStage s = t at hs
    obtain ⟨σ, j⟩ := t
    cases hc : (decide (j ≤ σ.length) &&
        (localDisj g σ (Nat.unpair m).1 j).isSome &&
        !localAccept a g σ (Nat.unpair m).1 (Nat.unpair m).2 j) with
    | false =>
      simp only [hc, Bool.cond_false, Option.elim_none] at hs
      exact hs.elim
    | true =>
      simp only [hc, Bool.cond_true, Option.elim_some] at hs
      have hσ := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 hs
      obtain ⟨⟨hj, hsome⟩, hacc⟩ : (j ≤ σ.length ∧
          (localDisj g σ (Nat.unpair m).1 j).isSome = true) ∧
          localAccept a g σ (Nat.unpair m).1 (Nat.unpair m).2 j = false := by
        simpa using hc
      rw [← hσ, localDisj_cantorPrefix g z _ hj] at hsome
      rw [← hσ, localAccept_cantorPrefix a g z _ _ hj] at hacc
      exact ⟨j, Option.isSome_iff_ne_none.1 hsome, hacc⟩

end Kolmogorov
