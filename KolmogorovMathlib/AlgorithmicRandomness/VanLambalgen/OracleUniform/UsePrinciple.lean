/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.Basic

/-!
# The use principle for families effectively open relative to `A ⊕ x`

A computation relative to the oracle `A ⊕ x` consults only finitely many bits of `x`. This module
turns that fact into a statement about effectively open families: every family that is uniformly
effectively open relative to `A ⊕ x` is the value at `x` of an oracle-uniform family relative to
`A` (`exists_isOracleUniformIn_uniformFamily_eq`). The oracle-uniform listing runs, for every
finite string `σ`, the bounded universal evaluator `PointToSet.oracleStage` on the finite prefix
of `A ⊕ σ` that `σ` determines; at a prefix of `x` it agrees with the evaluator relative to
`A ⊕ x`.

## Conventions

`A ⊕ z` is `PointToSet.oracleJoin A (seqOracle z)`, with `A` on the even queries. A stage `t` of
`oracleStage` reads only the queries below `t` (`Nat.unpair_left_le`), so it is determined by the
prefix of `z` of length `t`. Indices of the oracle-uniform listing code pairs `(t, i)`: the stage
`t` of the evaluator on the input coding `(n, i)`.

## Main declarations

* `exists_isOracleUniformIn_uniformFamily_eq` (blueprint node `vl:use-principle`): a family
  uniformly effectively open relative to `A ⊕ x` is `uniformFamily g x` for some `g`
  oracle-uniform relative to `A`.

Used by the direction `vl:snd` in `AlgorithmicRandomness/VanLambalgen/Directions/Right.lean`.
-/

namespace Kolmogorov

open PointToSet (oracleJoin)
open Nat.Partrec (Code)

variable {A : Set ℕ}

/-! ### Bounded evaluation on a finite oracle prefix -/

/-- Stage `t` of the bounded universal evaluator of the code `e` on the input `n`, run on the
finite oracle prefix `P`: the first success among the tests below `t`, each of which runs the
code for a bounded time on a truncation of `P`. -/
private def stageOnPrefix (P : List ℕ) (t e n : ℕ) : Option ℕ :=
  (List.range t).findSome? fun r =>
    Code.evaln (Nat.unpair r).2 (Denumerable.ofNat Code e)
      (Encodable.encode (P.take (Nat.unpair r).1, n))

/-- `List.findSome?` only depends on the values of the function on the members of the list. -/
private theorem findSome?_congr {α β : Type*} {f f' : α → Option β} :
    ∀ {l : List α}, (∀ r ∈ l, f r = f' r) → l.findSome? f = l.findSome? f'
  | [], _ => rfl
  | r :: l, h => by
    rw [List.findSome?_cons, List.findSome?_cons, h r List.mem_cons_self,
      findSome?_congr fun r' hr' => h r' (List.mem_cons_of_mem _ hr')]

open Classical in
/-- On the prefix of length `t` of an oracle, the prefix stage is the stage of
`PointToSet.oracleStage`. -/
private theorem stageOnPrefix_eq_oracleStage (B : Set ℕ) (t e n : ℕ) :
    stageOnPrefix ((List.range t).map fun k => if k ∈ B then 1 else 0) t e n =
      PointToSet.oracleStage B t e n := by
  unfold stageOnPrefix PointToSet.oracleStage
  refine findSome?_congr fun r hr => ?_
  have hr' : (Nat.unpair r).1 ≤ t :=
    (Nat.unpair_left_le r).trans (List.mem_range.1 hr).le
  rw [← List.map_take, List.take_range, Nat.min_eq_left hr']

/-- The prefix stage is computable in the prefix, the stage, the code and the input. -/
private theorem computable_stageOnPrefix :
    Computable fun p : List ℕ × ℕ × ℕ × ℕ => stageOnPrefix p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let test (p : List ℕ × ℕ × ℕ × ℕ) (r : ℕ) : Option ℕ :=
    Code.evaln (Nat.unpair r).2 (Denumerable.ofNat Code p.2.2.1)
      (Encodable.encode (p.1.take (Nat.unpair r).1, p.2.2.2))
  have htest : Computable₂ test := by
    have hu : Primrec fun q : (List ℕ × ℕ × ℕ × ℕ) × ℕ => Nat.unpair q.2 :=
      Primrec.unpair.comp Primrec.snd
    have htime : Primrec fun q : (List ℕ × ℕ × ℕ × ℕ) × ℕ => (Nat.unpair q.2).2 :=
      Primrec.snd.comp hu
    have hcode : Primrec fun q : (List ℕ × ℕ × ℕ × ℕ) × ℕ =>
        Denumerable.ofNat Code q.1.2.2.1 :=
      (Primrec.ofNat Code).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    have hinput : Primrec fun q : (List ℕ × ℕ × ℕ × ℕ) × ℕ =>
        Encodable.encode (q.1.1.take (Nat.unpair q.2).1, q.1.2.2.2) :=
      Primrec.encode.comp ((Primrec.list_take.comp (Primrec.fst.comp hu)
        (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
    exact (Code.primrec_evaln.comp ((htime.pair hcode).pair hinput)).to_comp
  have hor : Computable (fun p : Option ℕ × Option ℕ => p.1.or p.2) :=
    Primrec.option_orElse.to_comp.of_eq fun p => by cases p.1 <;> rfl
  have hstep : Computable₂ (fun (p : List ℕ × ℕ × ℕ × ℕ) (q : ℕ × Option ℕ) =>
      q.2.or (test p q.1)) :=
    (hor.comp ((Computable.snd.comp Computable.snd).pair
      (htest.comp Computable.fst (Computable.fst.comp Computable.snd)))).to₂
  have hrec := Computable.nat_rec (Computable.fst.comp Computable.snd)
    (Computable.const (none : Option ℕ)) hstep
  refine hrec.of_eq fun p => ?_
  change Nat.rec (motive := fun _ => Option ℕ) none (fun r acc => acc.or (test p r)) p.2.1 =
    (List.range p.2.1).findSome? (test p)
  generalize p.2.1 = t
  induction t with
  | zero => rfl
  | succ t ih =>
    simpa only [List.range_succ, List.findSome?_append, List.findSome?_singleton] using
      congrArg (fun o : Option ℕ => o.or (test p t)) ih

/-! ### The finite prefix of `A ⊕ σ` -/

open Classical in
/-- The characteristic values below `t` of `A ⊕ σ`, reading the bits of `σ` (padded with
`false`) on the odd queries. -/
private noncomputable def joinPrefix (A : Set ℕ) (σ : BitString) (t : ℕ) : List ℕ :=
  (List.range t).map fun k =>
    bif k % 2 == 0 then (if k / 2 ∈ A then 1 else 0) else (bif σ.getD (k / 2) false then 1 else 0)

open Classical in
/-- For a prefix of `z` of length at least `t`, `joinPrefix` is the characteristic prefix of
`A ⊕ z` of length `t`. -/
private theorem joinPrefix_cantorPrefix (z : CantorSeq) {ℓ t : ℕ} (ht : t ≤ ℓ) :
    joinPrefix A (cantorPrefix z ℓ) t =
      (List.range t).map fun k => if k ∈ oracleJoin A (seqOracle z) then 1 else 0 := by
  unfold joinPrefix
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < t := List.mem_range.1 hk
  by_cases h : k % 2 = 0
  · have hmem : k ∈ oracleJoin A (seqOracle z) ↔ k / 2 ∈ A := by
      simp [PointToSet.oracleJoin, h]
    simp [h, hmem]
  · have hmem : k ∈ oracleJoin A (seqOracle z) ↔ z (k / 2) = true := by
      simp [PointToSet.oracleJoin, h, seqOracle]
    have hget : (cantorPrefix z ℓ).getD (k / 2) false = z (k / 2) := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), cantorPrefix_getElem]
    rw [hget]
    simp [h, hmem]

/-- `joinPrefix` is computable relative to `A`. -/
private theorem computableIn_joinPrefix :
    ComputableIn {charOracle A} fun p : BitString × ℕ => joinPrefix A p.1 p.2 := by
  classical
  have hchar : ComputableIn {charOracle A} (fun k : ℕ => if k ∈ A then 1 else 0) :=
    PartrecIn.oracle (charOracle A) (Set.mem_singleton _)
  have hc : Primrec fun q : BitString × ℕ => q.2 % 2 == 0 :=
    Primrec.beq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)
  have hhalf : Primrec fun q : BitString × ℕ => q.2 / 2 :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hbit : Computable fun q : BitString × ℕ => bif q.1.getD (q.2 / 2) false then 1 else 0 :=
    Computable.cond ((Primrec.list_getD false).comp Primrec.fst hhalf).to_comp
      (Computable.const 1) (Computable.const 0)
  have hf : ComputableIn₂ {charOracle A} fun (σ : BitString) (k : ℕ) =>
      bif k % 2 == 0 then (if k / 2 ∈ A then 1 else 0)
      else (bif σ.getD (k / 2) false then 1 else 0) :=
    PointToSet.computable_in_cond hc.to_comp.computableIn
      (ComputableIn.comp hchar hhalf.to_comp.computableIn) hbit.computableIn
  exact ComputableIn.of_eq (computableIn_list_range_map hf) fun _ => rfl

/-! ### The oracle-uniform listing -/

/-- The oracle-uniform listing obtained from the index `e` of the bounded evaluator: at the
oracle prefix `σ`, level `n` and index coding `(t, i)` with `t ≤ |σ|`, it decodes the output of
stage `t` of the evaluator on the prefix of `A ⊕ σ` and the input coding `(n, i)`. -/
private noncomputable def useEnum (A : Set ℕ) (e : ℕ) (σ : BitString) (n j : ℕ) :
    Option BitString :=
  bif decide ((Nat.unpair j).1 ≤ σ.length) then
    (stageOnPrefix (joinPrefix A σ (Nat.unpair j).1) (Nat.unpair j).1 e
      (Nat.pair n (Nat.unpair j).2)).bind fun v =>
        (Encodable.decode v : Option (Option BitString)).getD none
  else none

/-- The listing `useEnum A e` is oracle-uniform relative to `A`. -/
private theorem isOracleUniformIn_useEnum (e : ℕ) : IsOracleUniformIn A (useEnum A e) := by
  have hu : Primrec fun p : BitString × ℕ × ℕ => Nat.unpair p.2.2 :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec fun p : BitString × ℕ × ℕ => (Nat.unpair p.2.2).1 := Primrec.fst.comp hu
  have hc : Primrec fun p : BitString × ℕ × ℕ => decide ((Nat.unpair p.2.2).1 ≤ p.1.length) :=
    Primrec.nat_le.decide.comp ht (Primrec.list_length.comp Primrec.fst)
  have hJ := ComputableIn.comp (computableIn_joinPrefix (A := A))
    (Primrec.fst.pair ht).to_comp.computableIn
  have hs := computable_stageOnPrefix.comp (Computable.snd.pair
    ((ht.comp Primrec.fst).to_comp.pair ((Computable.const e).pair
      (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (hu.comp Primrec.fst))).to_comp)))
  have hdec : Computable₂ fun (_ : (BitString × ℕ × ℕ) × List ℕ) (v : ℕ) =>
      (Encodable.decode v : Option (Option BitString)).getD none :=
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const none)).to_comp
  have hthen := ComputableIn.comp (Computable.option_bind hs hdec).computableIn
    (ComputableIn.id.pair hJ)
  exact (PointToSet.computable_in_cond hc.to_comp.computableIn hthen
    (ComputableIn.const (none : Option BitString))).of_eq fun _ => rfl

/-- At a prefix of `z` of length `k`, the listing at an index `(t, i)` with `t ≤ k` decodes the
stage `t` of the evaluator relative to `A ⊕ z`. -/
private theorem uniformEnum_useEnum (e : ℕ) (z : CantorSeq) (n : ℕ) {k t : ℕ} (i : ℕ)
    (hkt : t ≤ k) :
    uniformEnum (useEnum A e) z n (Nat.pair k (Nat.pair t i)) =
      (PointToSet.oracleStage (oracleJoin A (seqOracle z)) t e (Nat.pair n i)).bind fun v =>
        (Encodable.decode v : Option (Option BitString)).getD none := by
  classical
  simp only [uniformEnum, useEnum, Nat.unpair_pair, cantorPrefix_length,
    decide_eq_true hkt, Bool.cond_true]
  rw [joinPrefix_cantorPrefix z hkt, stageOnPrefix_eq_oracleStage]

/-- At an index `(t, i)` with `t` above the length of the oracle prefix, nothing is listed. -/
private theorem uniformEnum_useEnum_of_lt (e : ℕ) (z : CantorSeq) (n : ℕ) {k t : ℕ} (i : ℕ)
    (hkt : k < t) : uniformEnum (useEnum A e) z n (Nat.pair k (Nat.pair t i)) = none := by
  simp [uniformEnum, useEnum, Nat.not_le.2 hkt]

/-- Every family uniformly effectively open relative to `A ⊕ x` is the value at
`x` of a family oracle-uniform relative to `A`. Blueprint node `vl:use-principle`. -/
theorem exists_isOracleUniformIn_uniformFamily_eq {x : CantorSeq} {U : ℕ → Set CantorSeq}
    (hU : IsUniformlyEffectiveOpenIn (oracleJoin A (seqOracle x)) U) :
    ∃ g, IsOracleUniformIn A g ∧ ∀ n, uniformFamily g x n = U n := by
  obtain ⟨f, hf, hfU⟩ := hU
  have hu : Computable fun m : ℕ => Nat.unpair m := Computable.unpair
  have hc : ComputableIn {charOracle (oracleJoin A (seqOracle x))} fun m : ℕ =>
      Encodable.encode (f (Nat.unpair m).1 (Nat.unpair m).2) :=
    ComputableIn.comp Computable.encode.computableIn
      (hf.comp (ComputableIn.fst.comp hu.computableIn) (ComputableIn.snd.comp hu.computableIn))
  obtain ⟨e, he⟩ := PointToSet.oracleStage_universal (oracleJoin A (seqOracle x)) _ hc.partrecIn
  have hmem : ∀ n i v, v ∈ ((fun m : ℕ => Encodable.encode (f (Nat.unpair m).1
      (Nat.unpair m).2) : ℕ → ℕ) : ℕ →. ℕ) (Nat.pair n i) ↔ v = Encodable.encode (f n i) := by
    intro n i v
    simp [PFun.coe_val]
  refine ⟨useEnum A e, isOracleUniformIn_useEnum e, fun n => ?_⟩
  rw [hfU n]
  ext y
  simp only [uniformFamily, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k, j', rfl⟩ : ∃ k j', j = Nat.pair k j' := ⟨_, _, (Nat.pair_unpair j).symm⟩
    obtain ⟨t, i, rfl⟩ : ∃ t i, j' = Nat.pair t i := ⟨_, _, (Nat.pair_unpair j').symm⟩
    rcases le_or_gt t k with hkt | hkt
    · rw [coverSet, uniformEnum_useEnum e x n i hkt] at hj
      cases hs : PointToSet.oracleStage (oracleJoin A (seqOracle x)) t e (Nat.pair n i) with
      | none => simp [hs] at hj
      | some v =>
        have hv := (hmem n i v).1 ((he _ v).2 ⟨t, hs⟩)
        refine ⟨i, ?_⟩
        simpa [hs, hv, Encodable.encodek] using hj
    · simp [coverSet, uniformEnum_useEnum_of_lt e x n i hkt] at hj
  · rintro ⟨i, hi⟩
    obtain ⟨t, ht⟩ := (he (Nat.pair n i) (Encodable.encode (f n i))).1 ((hmem n i _).2 rfl)
    refine ⟨Nat.pair t (Nat.pair t i), ?_⟩
    rw [coverSet, uniformEnum_useEnum e x n i le_rfl, ht]
    simpa [Encodable.encodek] using hi

end Kolmogorov
