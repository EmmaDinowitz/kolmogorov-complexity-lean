/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Halves
import KolmogorovMathlib.AlgorithmicRandomness.Multiplicity
import KolmogorovMathlib.Oracle.Closure

/-!
# Families of open sets enumerated uniformly in an oracle sequence

An oracle-uniform family relative to `A` is a family of open sets `T z n` indexed by a sequence
`z` (the oracle) and a level `n`, whose cylinders are listed by one function
`g : BitString → ℕ → ℕ → Option BitString` computable in `A`: the member `T z n` is the union of
the cylinders `g σ n i` over all prefixes `σ` of `z` and all stages `i`. This module proves the
two facts that make such families useful for the van Lambalgen theorem:

* the joint set `{z ⊕ y | y ∈ T z n}` is uniformly effectively open relative to `A`
  (`IsOracleUniformIn.isUniformlyEffectiveOpenIn_jointSet`), since `z ⊕ y` extends a string `ρ`
  exactly when `z` extends `evenBits ρ` and `y` extends `oddBits ρ`;
* evaluated at a fixed oracle `x`, the family is uniformly effectively open relative to `A ⊕ x`
  (`IsOracleUniformIn.isUniformlyEffectiveOpenIn_uniformFamily`), since the prefixes of `x` are
  computable from `A ⊕ x`.

The sections `{y | z ⊕ y ∈ W n}` of a set `W` effectively open relative to `A` form an
oracle-uniform family (`isOracleUniformIn_sectionEnum`, `uniformFamily_sectionEnum`).

## Conventions

Oracles are sets of natural numbers queried through `charOracle`; `A ⊕ x` is
`PointToSet.oracleJoin A (seqOracle x)`. In `uniformEnum g z n j` the index `j` codes the pair
`(k, i)` by `Nat.pair`: the string `g (cantorPrefix z k) n i` is enumerated. The definitions
`IsOracleUniformIn`, `uniformEnum`, `uniformFamily` and `sectionEnum` are in
`VanLambalgen/Auxiliary/Defs.lean`. The general list lemma `computableIn_list_range_map`
(mapping a relatively computable function over `List.range N`) is proved here because the
relative computability API of `AlgorithmicRandomness/OracleComputability.lean` has no list
operations.

## Main declarations

* `IsOracleUniformIn.reindex` (blueprint node `vl:oracle-uniform`): a computable change of levels
  preserves oracle-uniformity.
* `IsOracleUniformIn.isUniformlyEffectiveOpenIn_jointSet` (blueprint node `vl:oracle-uniform`):
  joint sets of an oracle-uniform family are uniformly effectively open relative to `A`.
* `IsOracleUniformIn.isUniformlyEffectiveOpenIn_uniformFamily` (blueprint node
  `vl:oracle-uniform`): the family at `x` is uniformly effectively open relative to `A ⊕ x`.
* `uniformFamily_sectionEnum`, `isOracleUniformIn_sectionEnum` (blueprint node
  `vl:sections`): sections of an effectively open set form an oracle-uniform family.
* `computableIn_list_range_map` (blueprint node `vl:oracle-uniform`): relative computability of
  `fun a N => (List.range N).map (f a)`.

Used by `OracleUniform/UsePrinciple.lean`, `OracleUniform/Trim.lean` and the directions
`vl:snd`, `vl:converse` in `AlgorithmicRandomness/VanLambalgen/Directions/`.
-/

namespace Kolmogorov

open PointToSet (oracleJoin)

variable {A : Set ℕ}

/-! ### Relative computability of lists -/

/-- Mapping a function computable relative to `O` over `List.range N` is computable relative to
`O`, uniformly in the parameter and in `N`. Blueprint node `vl:oracle-uniform`. -/
theorem computableIn_list_range_map {O : Set (ℕ →. ℕ)} {α β : Type*} [Primcodable α]
    [Primcodable β] {f : α → ℕ → β} (hf : ComputableIn₂ O f) :
    ComputableIn₂ O fun a N => (List.range N).map (f a) := by
  have happ : Computable (fun p : List β × β => p.1 ++ [p.2]) :=
    Computable.list_append.comp Computable.fst
      (Computable.list_cons.comp Computable.snd (Computable.const []))
  have hstep : ComputableIn₂ O (fun (q : α × ℕ) (p : ℕ × List β) => p.2 ++ [f q.1 p.1]) :=
    (happ.computableIn.comp ((ComputableIn.snd.comp ComputableIn.snd).pair
      (hf.comp (ComputableIn.fst.comp ComputableIn.fst)
        (ComputableIn.fst.comp ComputableIn.snd)))).to₂
  refine (ComputableIn.nat_rec ComputableIn.snd (ComputableIn.const ([] : List β))
    hstep).of_eq ?_
  rintro ⟨a, N⟩
  change Nat.rec (motive := fun _ => List β) [] (fun k acc => acc ++ [f a k]) N =
    (List.range N).map (f a)
  induction N with
  | zero => rfl
  | succ N ih =>
    simpa only [List.range_succ, List.map_append, List.map_singleton] using
      congrArg (fun l : List β => l ++ [f a N]) ih

/-! ### Oracle-uniform families -/

/-- An oracle-uniform function stays oracle-uniform after a computable change of levels.
Blueprint node `vl:oracle-uniform`. -/
theorem IsOracleUniformIn.reindex {g : BitString → ℕ → ℕ → Option BitString}
    (hg : IsOracleUniformIn A g) {r : ℕ → ℕ} (hr : Computable r) :
    IsOracleUniformIn A fun σ n j => g σ (r n) j :=
  ComputableIn.comp hg (Computable.fst.pair ((hr.comp (Computable.fst.comp Computable.snd)).pair
    (Computable.snd.comp Computable.snd))).computableIn

/-! ### Joint sets -/

/-- The triple `(ρ, k, i)` coded by a stage of the enumeration of a joint set. -/
private def jointStage (s : ℕ) : BitString × ℕ × ℕ := (Encodable.decode s).getD ([], 0, 0)

/-- The cylinder listed at stage `s` for the joint set of level `n`: the string `ρ` when the
string listed for the prefix of length `k` of `evenBits ρ` at stage `i` is a prefix of
`oddBits ρ`. -/
private def jointEnum (g : BitString → ℕ → ℕ → Option BitString) (n s : ℕ) :
    Option BitString :=
  (g ((evenBits (jointStage s).1).take (jointStage s).2.1) n (jointStage s).2.2).bind fun τ =>
    bif bitPrefixCheck τ (oddBits (jointStage s).1) then some (jointStage s).1 else none

/-- The stages of a joint set are listed computably relative to `A`. -/
private theorem computableIn_jointEnum {g : BitString → ℕ → ℕ → Option BitString}
    (hg : IsOracleUniformIn A g) : ComputableIn₂ {charOracle A} (jointEnum g) := by
  have hst : Primrec fun p : ℕ × ℕ => jointStage p.2 :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const _)).comp Primrec.snd
  have hρ : Primrec fun p : ℕ × ℕ => (jointStage p.2).1 := Primrec.fst.comp hst
  have harg : Primrec fun p : ℕ × ℕ =>
      ((evenBits (jointStage p.2).1).take (jointStage p.2).2.1, p.1, (jointStage p.2).2.2) :=
    (Primrec.list_take.comp (Primrec.fst.comp (Primrec.snd.comp hst))
      (primrec_evenBits.comp hρ)).pair
        (Primrec.fst.pair (Primrec.snd.comp (Primrec.snd.comp hst)))
  have hgo := ComputableIn.comp hg harg.to_comp.computableIn
  have hρ' : Primrec fun r : ((ℕ × ℕ) × Option BitString) × BitString =>
      (jointStage r.1.1.2).1 := hρ.comp (Primrec.fst.comp Primrec.fst)
  have hH : Computable fun q : (ℕ × ℕ) × Option BitString =>
      q.2.bind fun τ =>
        bif bitPrefixCheck τ (oddBits (jointStage q.1.2).1) then some (jointStage q.1.2).1
        else none :=
    Computable.option_bind Computable.snd
      (Computable.cond (primrec₂_bitPrefixCheck.comp Primrec.snd
          (primrec_oddBits.comp hρ')).to_comp
        (Primrec.option_some.comp hρ').to_comp (Computable.const none))
  exact (hH.computableIn.comp (ComputableIn.id.pair hgo)).of_eq fun _ => rfl

/-- A point of a joint set lies in a cylinder listed for it. -/
private theorem exists_jointEnum_of_mem {g : BitString → ℕ → ℕ → Option BitString} {n j : ℕ}
    {w : CantorSeq} (hw : cantorOdds w ∈ coverSet (uniformEnum g (cantorEvens w) n) j) :
    ∃ s, w ∈ (jointEnum g n s).elim ∅ cantorCylinder := by
  obtain ⟨k, i, rfl⟩ : ∃ k i, j = Nat.pair k i := ⟨_, _, (Nat.pair_unpair j).symm⟩
  have hτ' : uniformEnum g (cantorEvens w) n (Nat.pair k i) =
      g (cantorPrefix (cantorEvens w) k) n i := by simp [uniformEnum]
  rw [coverSet, hτ'] at hw
  cases hτ : g (cantorPrefix (cantorEvens w) k) n i with
  | none => simp [hτ] at hw
  | some τ =>
    rw [hτ, Option.elim_some] at hw
    refine ⟨Encodable.encode (cantorPrefix w (2 * (k + τ.length)), k, i), ?_⟩
    have hstage : jointStage (Encodable.encode (cantorPrefix w (2 * (k + τ.length)), k, i)) =
        (cantorPrefix w (2 * (k + τ.length)), k, i) := by
      simp [jointStage, Encodable.encodek]
    have htake : (evenBits (cantorPrefix w (2 * (k + τ.length)))).take k =
        cantorPrefix (cantorEvens w) k := by
      rw [evenBits_cantorPrefix, cantorPrefix_take _ _ _ (by omega)]
    have hpre : τ <+: oddBits (cantorPrefix w (2 * (k + τ.length))) := by
      rw [oddBits_cantorPrefix]
      have h1 := (isCantorPrefix_iff_cantorPrefix_eq τ (cantorOdds w)).1 hw
      calc τ = cantorPrefix (cantorOdds w) τ.length := h1.symm
        _ <+: cantorPrefix (cantorOdds w) (k + τ.length) := cantorPrefix_mono _ (by omega)
    simp only [jointEnum, hstage, htake, hτ, Option.bind_some, (bitPrefixCheck_iff _ _).2 hpre,
      Bool.cond_true, Option.elim_some]
    exact (isCantorPrefix_iff_cantorPrefix_eq _ _).2 (by simp)

/-- A point of a listed cylinder lies in the joint set. -/
private theorem mem_of_jointEnum {g : BitString → ℕ → ℕ → Option BitString} {n s : ℕ}
    {w : CantorSeq} (hs : w ∈ (jointEnum g n s).elim ∅ cantorCylinder) :
    cantorOdds w ∈ uniformFamily g (cantorEvens w) n := by
  unfold jointEnum at hs
  generalize jointStage s = t at hs
  obtain ⟨ρ, k, i⟩ := t
  cases hτ : g ((evenBits ρ).take k) n i with
  | none => simp [hτ] at hs
  | some τ =>
    cases hb : bitPrefixCheck τ (oddBits ρ) with
    | false => simp [hτ, hb] at hs
    | true =>
      have hwρ : w ∈ cantorCylinder ρ := by simpa [hτ, hb] using hs
      obtain ⟨he, ho⟩ := (mem_cantorCylinder_iff_halves ρ w).1 hwρ
      have hoτ : cantorOdds w ∈ cantorCylinder τ :=
        cantorCylinder_subset_of_prefix ((bitPrefixCheck_iff τ (oddBits ρ)).1 hb) ho
      have hev := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 he
      obtain ⟨k', hk'⟩ : ∃ k', (evenBits ρ).take k = cantorPrefix (cantorEvens w) k' := by
        rcases le_total k (evenBits ρ).length with hk | hk
        · refine ⟨k, ?_⟩
          calc (evenBits ρ).take k
              = (cantorPrefix (cantorEvens w) (evenBits ρ).length).take k := by rw [hev]
            _ = cantorPrefix (cantorEvens w) k := cantorPrefix_take _ _ _ hk
        · exact ⟨(evenBits ρ).length, by rw [List.take_of_length_le hk, hev]⟩
      refine Set.mem_iUnion.2 ⟨Nat.pair k' i, ?_⟩
      simp only [coverSet, uniformEnum, Nat.unpair_pair, ← hk', hτ, Option.elim_some]
      exact hoτ

/-- For an oracle-uniform family relative to `A`, the joint
sets `{z ⊕ y | y ∈ T z n}` form a uniformly effectively open family relative to `A`.
Blueprint node `vl:oracle-uniform`. -/
theorem IsOracleUniformIn.isUniformlyEffectiveOpenIn_jointSet
    {g : BitString → ℕ → ℕ → Option BitString} (hg : IsOracleUniformIn A g) :
    IsUniformlyEffectiveOpenIn A fun n => jointSet fun z => uniformFamily g z n := by
  refine ⟨jointEnum g, computableIn_jointEnum hg, fun n => ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (show cantorOdds w ∈ uniformFamily g (cantorEvens w) n
      from hw)
    exact Set.mem_iUnion.2 (exists_jointEnum_of_mem hj)
  · intro hw
    obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hw
    exact mem_of_jointEnum hs

/-! ### Evaluation at a fixed oracle -/

/-- The prefix of length `k` of a sequence is a list of its first `k` values. -/
private theorem cantorPrefix_eq_map_range (w : CantorSeq) (k : ℕ) :
    cantorPrefix w k = (List.range k).map w := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- The prefixes of `x` are computable relative to `A ⊕ x`. -/
private theorem computableIn_cantorPrefix (x : CantorSeq) :
    ComputableIn {charOracle (oracleJoin A (seqOracle x))} (cantorPrefix x) := by
  classical
  have hchar : ComputableIn {charOracle (oracleJoin A (seqOracle x))}
      (fun k : ℕ => if k ∈ oracleJoin A (seqOracle x) then 1 else 0) :=
    PartrecIn.oracle (charOracle (oracleJoin A (seqOracle x))) (Set.mem_singleton _)
  have hq : Computable fun k : ℕ => 2 * k + 1 :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1)).to_comp
  have hbeq : Computable fun m : ℕ => m == 1 :=
    (Primrec.beq.comp Primrec.id (Primrec.const 1)).to_comp
  have hbit : ComputableIn {charOracle (oracleJoin A (seqOracle x))} x := by
    refine (hbeq.computableIn.comp (hchar.comp hq.computableIn)).of_eq fun k => ?_
    have hmem : 2 * k + 1 ∈ oracleJoin A (seqOracle x) ↔ x k = true := by
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      simp [PointToSet.oracleJoin, seqOracle, h1, h2]
    cases hxk : x k
    · have hn : 2 * k + 1 ∉ oracleJoin A (seqOracle x) := fun h => by
        rw [hmem.1 h] at hxk
        exact Bool.noConfusion hxk
      simp [hn]
    · simp [hmem.2 hxk]
  have hmap := computableIn_list_range_map (f := fun (_ : ℕ) k => x k)
    (ComputableIn.comp hbit ComputableIn.snd)
  exact (ComputableIn.comp hmap (ComputableIn.id.pair ComputableIn.id)).of_eq fun k =>
    (cantorPrefix_eq_map_range x k).symm

/-- An oracle-uniform family relative to `A`, evaluated at the
sequence `x`, is uniformly effectively open relative to `A ⊕ x`.
Blueprint node `vl:oracle-uniform`. -/
theorem IsOracleUniformIn.isUniformlyEffectiveOpenIn_uniformFamily
    {g : BitString → ℕ → ℕ → Option BitString} (hg : IsOracleUniformIn A g) (x : CantorSeq) :
    IsUniformlyEffectiveOpenIn (oracleJoin A (seqOracle x)) (uniformFamily g x) := by
  have hgB := PointToSet.computableIn_mono_oracle hg (PointToSet.oracle_joins A (seqOracle x))
  refine ⟨uniformEnum g x, ?_, fun n => rfl⟩
  have hu : Computable fun p : ℕ × ℕ => Nat.unpair p.2 := Computable.unpair.comp Computable.snd
  exact (ComputableIn.comp hgB
    ((ComputableIn.comp (computableIn_cantorPrefix x)
      (ComputableIn.fst.comp hu.computableIn)).pair
        (ComputableIn.fst.pair (ComputableIn.snd.comp hu.computableIn)))).of_eq fun _ => rfl

/-! ### Sections of an effectively open set -/

/-- The family listed by `sectionEnum f` at the oracle `z` is the family of sections at `z` of the
open sets listed by `f`. Blueprint node `vl:sections`. -/
theorem uniformFamily_sectionEnum (f : ℕ → ℕ → Option BitString) (z : CantorSeq) (m : ℕ) :
    uniformFamily (sectionEnum f) z m =
      {y | cantorJoin z y ∈ ⋃ i, (f m i).elim ∅ cantorCylinder} := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, uniformFamily]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k, i, rfl⟩ : ∃ k i, j = Nat.pair k i := ⟨_, _, (Nat.pair_unpair j).symm⟩
    simp only [coverSet, uniformEnum, Nat.unpair_pair, sectionEnum] at hj
    cases hρ : f m i with
    | none => simp only [hρ, Option.bind_none, Option.elim_none] at hj; exact hj.elim
    | some ρ =>
      cases hb : decide (evenBits ρ = cantorPrefix z k) with
      | false =>
        simp only [hρ, Option.bind_some, hb, Bool.cond_false, Option.elim_none] at hj
        exact hj.elim
      | true =>
        simp only [hρ, Option.bind_some, hb, Bool.cond_true, Option.elim_some] at hj
        have hze : z ∈ cantorCylinder (evenBits ρ) := by
          rw [of_decide_eq_true hb]
          exact (isCantorPrefix_iff_cantorPrefix_eq _ _).2 (by simp)
        refine ⟨i, ?_⟩
        rw [hρ, Option.elim_some, mem_cantorCylinder_iff_halves, cantorEvens_cantorJoin,
          cantorOdds_cantorJoin]
        exact ⟨hze, hj⟩
  · rintro ⟨i, hi⟩
    cases hρ : f m i with
    | none => rw [hρ, Option.elim_none] at hi; exact hi.elim
    | some ρ =>
      rw [hρ, Option.elim_some, mem_cantorCylinder_iff_halves, cantorEvens_cantorJoin,
        cantorOdds_cantorJoin] at hi
      obtain ⟨hze, hyo⟩ := hi
      have hz := (isCantorPrefix_iff_cantorPrefix_eq _ _).1 hze
      refine ⟨Nat.pair (evenBits ρ).length i, ?_⟩
      simp only [coverSet, uniformEnum, Nat.unpair_pair, sectionEnum, hρ, hz, Option.bind_some]
      exact hyo

/-- The sections of a set listed computably relative to `A` form an oracle-uniform family
relative to `A`. Blueprint node `vl:sections`. -/
theorem isOracleUniformIn_sectionEnum {f : ℕ → ℕ → Option BitString}
    (hf : ComputableIn₂ {charOracle A} f) : IsOracleUniformIn A (sectionEnum f) := by
  have hfi : ComputableIn {charOracle A} fun p : BitString × ℕ × ℕ => f p.2.1 p.2.2 :=
    hf.comp (ComputableIn.fst.comp ComputableIn.snd) (ComputableIn.snd.comp ComputableIn.snd)
  have hH : Computable fun q : (BitString × ℕ × ℕ) × Option BitString =>
      q.2.bind fun ρ => bif decide (evenBits ρ = q.1.1) then some (oddBits ρ) else none :=
    Computable.option_bind Computable.snd
      (Computable.cond (Primrec.eq.decide.comp (primrec_evenBits.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).to_comp
        (Primrec.option_some.comp (primrec_oddBits.comp Primrec.snd)).to_comp
        (Computable.const none))
  exact (hH.computableIn.comp (ComputableIn.id.pair hfi)).of_eq fun _ => rfl

end Kolmogorov
