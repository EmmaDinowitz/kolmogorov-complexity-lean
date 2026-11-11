/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.Oracle.PrefixComplexity.Basic
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Two-stage oracle prefix machines and the conditional calculus of `K^A`

The optimal oracle prefix machine `optimalOraclePrefix A` of
`KolmogorovMathlib.Oracle.Universal` is only known, so far, through its unconditional
complexity `oracleComplexity`.  This file provides the conditional calculus that the
split-precision theory of `KolmogorovMathlib.PointToSet.SplitPrecision` needs, all relative
to an arbitrary oracle `A`:

* `twoStageMachine U g h`: on the program `p₁ ++ p₂` in context `z`, run `U` on `p₁` in
  context `z` to obtain `y`, then run `U` on `p₂` in the context `g z y p₁.length`, obtaining
  `x`, and output `h z y x`.  Because the domain of a prefix machine is prefix-free in every
  context, the parse is unique (`TwoStageSpec.eq_of_prefix`), so the machine is again a prefix
  machine (`twoStageMachine_isPrefixMachine`) and it is `A`-computable when `U`, `g`, `h` are
  (`twoStageMachine_isDecompressorIn`).
* `oraclePrefixComplexityNat_twoStage_le`: the resulting bound
  `K^A(h z y x | z) ≤ K^A(y | z) + K^A(x | g z y K^A(y | z)) + O(1)`, with its three standard
  instances: the chain rule `oraclePrefixComplexityNat_triangle`
  (`K(x | z) ≤ K(y | z) + K(x | y) + O(1)`), the coding direction of symmetry of information
  `oraclePrefixComplexityNat_pair_le_cond_context`
  (`K(⟨y, x⟩ | z) ≤ K(y | z) + K(x | y, K(y | z)) + O(1)`) and conditional concatenation
  `oraclePrefixComplexityNat_pair_le_add` (`K(⟨y, x⟩ | z) ≤ K(y | z) + K(x | z) + O(1)`).
* Recoding: `oraclePrefixComplexityNat_cond_le_of_partrecIn` (replacing the condition by an
  `A`-computable image of it) and `oraclePrefixComplexityNat_map_le_of_partrecIn`,
  `oraclePrefixComplexityNat_map_cond_le` (post-processing the output), each at a constant
  cost depending only on `A` and the operation.

All constants are explicit existential naturals, following the conventions of
`KolmogorovMathlib.Oracle.PrefixComplexity.Basic`.  Blueprint nodes `split:two-stage`,
`split:chain-rule`, `split:recoding`.
-/

namespace Kolmogorov.PointToSet

open scoped Computability

/-! ### Natural-number shadows -/

/-- A bound on the extended conditional complexity of the optimal oracle machine transfers
to its natural shadow. Blueprint node `split:two-stage`. -/
theorem oraclePrefixComplexityNat_le_of_KP_le {A : Set ℕ} {x y : BitString} {n : ℕ}
    (h : KP (optimalOraclePrefix A) x y ≤ (n : ENat)) :
    oraclePrefixComplexityNat A x y ≤ n := by
  have h' : oraclePrefixComplexity A x y ≤ (n : ENat) := h
  rw [← oraclePrefixComplexity_coe] at h'
  exact ENat.natCast_le_natCast.mp h'

/-- The natural shadow bounds the extended conditional complexity. -/
theorem KP_le_oraclePrefixComplexityNat (A : Set ℕ) (x y : BitString) :
    KP (optimalOraclePrefix A) x y ≤ (oraclePrefixComplexityNat A x y : ENat) :=
  (oraclePrefixComplexity_coe A x y).symm.le

/-- Every string has a shortest `A`-program in every context, of length exactly the natural
conditional complexity. Blueprint node `split:two-stage`. -/
theorem exists_program_oraclePrefix (A : Set ℕ) (x y : BitString) :
    ∃ p : BitString, produces (optimalOraclePrefix A) p y x ∧
      p.length = oraclePrefixComplexityNat A x y := by
  obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top (exists_optimalOraclePrefix_finite A x y)
  refine ⟨p, hp, ?_⟩
  apply ENat.natCast_inj.mp
  exact hlen.trans (oraclePrefixComplexity_coe A x y).symm

/-! ### The two-stage machine -/

/-- The parse relation of the two-stage machine: `w` splits as `p₁ ++ p₂`, where `p₁`
produces `y` in context `z` and `p₂` produces `x` in the derived context `g z y p₁.length`,
and the output is `h z y x`. Blueprint node `split:two-stage`. -/
def TwoStageSpec (U : Map) (g : BitString → BitString → ℕ → BitString)
    (h : BitString → BitString → BitString → BitString) (w z out : BitString) : Prop :=
  ∃ p₁ p₂ y x : BitString, w = p₁ ++ p₂ ∧ produces U p₁ z y ∧
    produces U p₂ (g z y p₁.length) x ∧ out = h z y x

/-- For a prefix machine the two-stage parse of a string is unique, and two prefix-comparable
parsable strings coincide. Blueprint node `split:two-stage`. -/
theorem TwoStageSpec.eq_of_prefix {U : Map} (hU : IsPrefixMachine U)
    {g : BitString → BitString → ℕ → BitString}
    {h : BitString → BitString → BitString → BitString} {w w' z out out' : BitString}
    (hw : TwoStageSpec U g h w z out) (hw' : TwoStageSpec U g h w' z out')
    (hpre : w <+: w') : w = w' ∧ out = out' := by
  obtain ⟨p₁, p₂, y, x, rfl, hp₁, hp₂, rfl⟩ := hw
  obtain ⟨q₁, q₂, y', x', rfl, hq₁, hq₂, rfl⟩ := hw'
  have h1 : p₁ = q₁ := by
    rcases List.prefix_or_prefix_of_prefix ((List.prefix_append p₁ p₂).trans hpre)
      (List.prefix_append q₁ q₂) with h | h
    · exact hU.eq_of_prefix hp₁ hq₁ h
    · exact (hU.eq_of_prefix hq₁ hp₁ h).symm
  subst h1
  have hy : y = y' := Part.mem_unique hp₁ hq₁
  subst hy
  have h2 : p₂ <+: q₂ := (List.prefix_append_right_inj p₁).mp hpre
  have h2' : p₂ = q₂ := hU.eq_of_prefix hp₂ hq₂ h2
  subst h2'
  have hx : x = x' := Part.mem_unique hp₂ hq₂
  subst hx
  exact ⟨rfl, rfl⟩

/-- The two-stage machine: defined exactly on the strings admitting a two-stage parse, with
the parse's output. Blueprint node `split:two-stage`. -/
noncomputable def twoStageMachine (U : Map) (g : BitString → BitString → ℕ → BitString)
    (h : BitString → BitString → BitString → BitString) : Map := fun pr =>
  Part.mk (∃ out, TwoStageSpec U g h pr.1 pr.2 out) fun hex => Classical.choose hex

/-- Membership in the two-stage machine is the parse relation (for a prefix machine `U`).
Blueprint node `split:two-stage`. -/
theorem mem_twoStageMachine_iff {U : Map} (hU : IsPrefixMachine U)
    {g : BitString → BitString → ℕ → BitString}
    {h : BitString → BitString → BitString → BitString} {w z out : BitString} :
    out ∈ twoStageMachine U g h (w, z) ↔ TwoStageSpec U g h w z out := by
  simp only [twoStageMachine, Part.mem_mk_iff]
  constructor
  · rintro ⟨hex, rfl⟩
    exact Classical.choose_spec hex
  · intro hs
    refine ⟨⟨out, hs⟩, ?_⟩
    exact (TwoStageSpec.eq_of_prefix hU (Classical.choose_spec (⟨out, hs⟩ : ∃ o,
      TwoStageSpec U g h w z o)) hs List.prefix_rfl).2

/-- The two-stage machine of a prefix machine is a prefix machine.
Blueprint node `split:two-stage`. -/
theorem twoStageMachine_isPrefixMachine {U : Map} (hU : IsPrefixMachine U)
    (g : BitString → BitString → ℕ → BitString)
    (h : BitString → BitString → BitString → BitString) :
    IsPrefixMachine (twoStageMachine U g h) := by
  intro z p hp q hq hpre
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hp
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hq
  exact (TwoStageSpec.eq_of_prefix hU ((mem_twoStageMachine_iff hU).mp ha)
    ((mem_twoStageMachine_iff hU).mp hb) hpre).1

/-- Concatenating a first-stage and a second-stage program yields a two-stage program for the
combined output. Blueprint node `split:two-stage`. -/
theorem twoStageMachine_produces {U : Map} (hU : IsPrefixMachine U)
    {g : BitString → BitString → ℕ → BitString}
    {h : BitString → BitString → BitString → BitString} {p₁ p₂ z y x : BitString}
    (h₁ : produces U p₁ z y) (h₂ : produces U p₂ (g z y p₁.length) x) :
    produces (twoStageMachine U g h) (p₁ ++ p₂) z (h z y x) :=
  (mem_twoStageMachine_iff hU).mpr ⟨p₁, p₂, y, x, rfl, h₁, h₂, rfl⟩

/-- The two-stage machine of an `A`-computable prefix machine, with `A`-computable context
and output maps, is `A`-computable: it enumerates the halting pairs of segments and searches
for the split. Blueprint node `split:two-stage`. -/
theorem twoStageMachine_isDecompressorIn (A : Set ℕ) {U : Map}
    (hU : IsDecompressorIn (charOracle A) U) (hpre : IsPrefixMachine U)
    {g : BitString → BitString → ℕ → BitString}
    (hg : ComputableIn {charOracle A} fun q : BitString × BitString × ℕ => g q.1 q.2.1 q.2.2)
    {h : BitString → BitString → BitString → BitString}
    (hh : ComputableIn {charOracle A}
      fun q : BitString × BitString × BitString => h q.1 q.2.1 q.2.2) :
    IsDecompressorIn (charOracle A) (twoStageMachine U g h) := by
  rw [isDecompressorIn_iff_partrecIn] at hU ⊢
  -- Running both stages on a triple `(p₁, p₂, z)`, returning the pair of outputs.
  let R : BitString × BitString × BitString →. BitString × BitString := fun t =>
    (U (t.1, t.2.2)).bind fun y => (U (t.2.1, g t.2.2 y t.1.length)).map fun x => (y, x)
  have hR : PartrecIn {charOracle A} R := by
    have h1 : PartrecIn {charOracle A}
        (fun t : BitString × BitString × BitString => U (t.1, t.2.2)) :=
      hU.comp (ComputableIn.fst.pair (ComputableIn.snd.comp ComputableIn.snd))
    have hctx : ComputableIn {charOracle A}
        (fun q : (BitString × BitString × BitString) × BitString =>
          (q.1.2.1, g q.1.2.2 q.2 q.1.1.length)) := by
      refine ComputableIn.pair (ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.fst)) ?_
      exact hg.comp (ComputableIn.pair
        (ComputableIn.snd.comp (ComputableIn.snd.comp ComputableIn.fst))
        (ComputableIn.pair ComputableIn.snd
          (Primrec.list_length.to_comp.computableIn.comp
            (ComputableIn.fst.comp ComputableIn.fst))))
    have hrun : PartrecIn {charOracle A}
        (fun q : (BitString × BitString × BitString) × BitString =>
          U (q.1.2.1, g q.1.2.2 q.2 q.1.1.length)) := hU.comp hctx
    have hout : ComputableIn₂ {charOracle A}
        (fun (q : (BitString × BitString × BitString) × BitString) (x : BitString) =>
          (q.2, x)) :=
      ComputableIn.pair (ComputableIn.snd.comp ComputableIn.fst) ComputableIn.snd
    exact h1.bind (hrun.map hout)
  -- The halting triples are relatively enumerable.
  have hRE : IsREIn A (fun t : BitString × BitString × BitString => (R t).Dom) :=
    ⟨fun t => (R t).map fun _ => (0 : ℕ), hR.map (ComputableIn.const 0), fun _ => Iff.rfl⟩
  obtain ⟨e, he, henum⟩ := (relative_enumeration A _).mp hRE
  -- Search the enumeration for a triple whose segments concatenate to the program.
  let test : BitString × BitString → ℕ → Option (BitString × BitString × BitString) :=
    fun wz t => (e t).bind fun tr => if (tr.1 ++ tr.2.1, tr.2.2) = wz then some tr else none
  have hlocal : Computable (fun q : (BitString × BitString) ×
      Option (BitString × BitString × BitString) =>
        q.2.bind fun tr => if (tr.1 ++ tr.2.1, tr.2.2) = q.1 then some tr else none) := by
    have hdec : Computable (fun q : (BitString × BitString) ×
        (BitString × BitString × BitString) => decide ((q.2.1 ++ q.2.2.1, q.2.2.2) = q.1)) :=
      (Primrec.eq.comp (Primrec.pair
        (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) Primrec.fst).decide.to_comp
    have hm : Computable (fun q : (BitString × BitString) ×
        (BitString × BitString × BitString) =>
          if (q.2.1 ++ q.2.2.1, q.2.2.2) = q.1 then some q.2 else none) :=
      (Computable.cond hdec (Computable.option_some.comp Computable.snd)
        (Computable.const none)).of_eq fun _ => by simp only [Bool.cond_decide]
    exact Computable.option_bind Computable.snd
      (hm.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  have htest : ComputableIn₂ {charOracle A} test :=
    (hlocal.computableIn.comp (ComputableIn.fst.pair (he.comp ComputableIn.snd))).to₂
  have hmem (wz : BitString × BitString) (tr : BitString × BitString × BitString) (t : ℕ) :
      tr ∈ test wz t ↔ e t = some tr ∧ (tr.1 ++ tr.2.1, tr.2.2) = wz := by
    simp only [test, Option.mem_def, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨tr', htr', hif⟩
      split_ifs at hif with hcond
      · cases Option.some.inj hif
        exact ⟨htr', hcond⟩
    · rintro ⟨htr, hcond⟩
      exact ⟨tr, htr, by simp [hcond]⟩
  let S : BitString × BitString →. BitString × BitString × BitString :=
    fun wz => Nat.rfindOpt (test wz)
  have hS : PartrecIn {charOracle A} S := PartrecIn.rfindOpt htest
  have hsound (wz : BitString × BitString) (tr : BitString × BitString × BitString)
      (htr : tr ∈ S wz) : (tr.1 ++ tr.2.1, tr.2.2) = wz ∧ (R tr).Dom := by
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec htr
    obtain ⟨het, hcond⟩ := (hmem wz tr t).mp ht
    exact ⟨hcond, (henum tr).mpr ⟨t, het⟩⟩
  have hdom (wz : BitString × BitString) (tr : BitString × BitString × BitString)
      (hcond : (tr.1 ++ tr.2.1, tr.2.2) = wz) (hR' : (R tr).Dom) : (S wz).Dom := by
    obtain ⟨t, ht⟩ := (henum tr).mp hR'
    exact Nat.rfindOpt_dom.mpr ⟨t, tr, (hmem wz tr t).mpr ⟨ht, hcond⟩⟩
  -- The machine: find the split, run both stages, post-process.
  let F : BitString × BitString →. BitString := fun wz =>
    (S wz).bind fun tr => (R tr).map fun yx => h wz.2 yx.1 yx.2
  have hF : PartrecIn {charOracle A} F := by
    have hpost : ComputableIn₂ {charOracle A}
        (fun (q : (BitString × BitString) × (BitString × BitString × BitString))
          (yx : BitString × BitString) => h q.1.2 yx.1 yx.2) :=
      ComputableIn₂.mk ((hh.comp (ComputableIn.pair
        (ComputableIn.snd.comp (ComputableIn.fst.comp ComputableIn.fst))
        (ComputableIn.pair (ComputableIn.fst.comp ComputableIn.snd)
          (ComputableIn.snd.comp ComputableIn.snd)))).of_eq fun _ => rfl)
    exact hS.bind ((hR.comp ComputableIn.snd).map hpost)
  -- The machine has exactly the two-stage parse relation as its graph.
  have hRmem (tr : BitString × BitString × BitString) (yx : BitString × BitString) :
      yx ∈ R tr ↔ produces U tr.1 tr.2.2 yx.1 ∧
        produces U tr.2.1 (g tr.2.2 yx.1 tr.1.length) yx.2 := by
    simp only [R, Part.mem_bind_iff, Part.mem_map_iff]
    constructor
    · rintro ⟨y, hy, x, hx, rfl⟩
      exact ⟨hy, hx⟩
    · rintro ⟨hy, hx⟩
      exact ⟨yx.1, hy, yx.2, hx, rfl⟩
  refine hF.of_eq fun wz => ?_
  obtain ⟨w, z⟩ := wz
  apply Part.ext
  intro out
  rw [mem_twoStageMachine_iff hpre]
  simp only [F, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨tr, htr, yx, hyx, rfl⟩
    obtain ⟨hcond, -⟩ := hsound (w, z) tr htr
    obtain ⟨hy, hx⟩ := (hRmem tr yx).mp hyx
    have hw : tr.1 ++ tr.2.1 = w := congrArg Prod.fst hcond
    have hz : tr.2.2 = z := congrArg Prod.snd hcond
    refine ⟨tr.1, tr.2.1, yx.1, yx.2, hw.symm, ?_, ?_, ?_⟩
    · rw [← hz]; exact hy
    · rw [← hz]; exact hx
    · rw [← hz]
  · rintro ⟨p₁, p₂, y, x, rfl, hp₁, hp₂, rfl⟩
    have hRdom : (R (p₁, p₂, z)).Dom :=
      Part.dom_iff_mem.mpr ⟨(y, x), (hRmem (p₁, p₂, z) (y, x)).mpr ⟨hp₁, hp₂⟩⟩
    obtain ⟨tr, htr⟩ := Part.dom_iff_mem.mp (hdom (p₁ ++ p₂, z) (p₁, p₂, z) rfl hRdom)
    obtain ⟨hcond, hRtr⟩ := hsound (p₁ ++ p₂, z) tr htr
    obtain ⟨yx, hyx⟩ := Part.dom_iff_mem.mp hRtr
    refine ⟨tr, htr, yx, hyx, ?_⟩
    obtain ⟨hy, hx⟩ := (hRmem tr yx).mp hyx
    have hw : tr.1 ++ tr.2.1 = p₁ ++ p₂ := congrArg Prod.fst hcond
    have hz : tr.2.2 = z := congrArg Prod.snd hcond
    have hspec : TwoStageSpec U g h (p₁ ++ p₂) z (h z yx.1 yx.2) := by
      refine ⟨tr.1, tr.2.1, yx.1, yx.2, hw.symm, ?_, ?_, rfl⟩
      · rw [← hz]; exact hy
      · rw [← hz]; exact hx
    exact (TwoStageSpec.eq_of_prefix hpre hspec ⟨p₁, p₂, y, x, rfl, hp₁, hp₂, rfl⟩
      List.prefix_rfl).2

/-! ### The two-stage bound and its instances -/

/-- **Two-stage bound.** For `A`-computable context and output maps,
`K^A(h z y x | z) ≤ K^A(y | z) + K^A(x | g z y K^A(y | z)) + O(1)`.
Blueprint node `split:two-stage`. -/
theorem oraclePrefixComplexityNat_twoStage_le (A : Set ℕ)
    {g : BitString → BitString → ℕ → BitString}
    (hg : ComputableIn {charOracle A} fun q : BitString × BitString × ℕ => g q.1 q.2.1 q.2.2)
    {h : BitString → BitString → BitString → BitString}
    (hh : ComputableIn {charOracle A}
      fun q : BitString × BitString × BitString => h q.1 q.2.1 q.2.2) :
    ∃ c : ℕ, ∀ z y x : BitString,
      oraclePrefixComplexityNat A (h z y x) z ≤
        oraclePrefixComplexityNat A y z +
          oraclePrefixComplexityNat A x (g z y (oraclePrefixComplexityNat A y z)) + c := by
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec A
  obtain ⟨c, hc⟩ := hopt _ (twoStageMachine_isDecompressorIn A hUd hUp hg hh)
    (twoStageMachine_isPrefixMachine hUp g h)
  refine ⟨c, fun z y x => ?_⟩
  obtain ⟨p₁, hp₁, hl₁⟩ := exists_program_oraclePrefix A y z
  obtain ⟨p₂, hp₂, hl₂⟩ :=
    exists_program_oraclePrefix A x (g z y (oraclePrefixComplexityNat A y z))
  rw [← hl₁] at hp₂
  have hprod := twoStageMachine_produces (h := h) hUp hp₁ hp₂
  have hbound : KP (optimalOraclePrefix A) (h z y x) z ≤
      ((p₁.length + p₂.length + c : ℕ) : ENat) := by
    calc KP (optimalOraclePrefix A) (h z y x) z
        ≤ KP (twoStageMachine (optimalOraclePrefix A) g h) (h z y x) z + (c : ENat) :=
          hc (h z y x) z
      _ ≤ ((p₁ ++ p₂).length : ENat) + (c : ENat) := by
          gcongr; exact KP_le_programLength_of_produces hprod
      _ = ((p₁.length + p₂.length + c : ℕ) : ENat) := by
          rw [List.length_append]; norm_cast
  have := oraclePrefixComplexityNat_le_of_KP_le hbound
  omega

/-- **Chain rule** (conditional triangle inequality):
`K^A(x | z) ≤ K^A(y | z) + K^A(x | y) + O(1)`. Blueprint node `split:chain-rule`. -/
theorem oraclePrefixComplexityNat_triangle (A : Set ℕ) :
    ∃ c : ℕ, ∀ x y z : BitString,
      oraclePrefixComplexityNat A x z ≤
        oraclePrefixComplexityNat A y z + oraclePrefixComplexityNat A x y + c := by
  have hg : ComputableIn {charOracle A}
      fun q : BitString × BitString × ℕ => (fun (_ : BitString) (y : BitString) (_ : ℕ) => y)
        q.1 q.2.1 q.2.2 :=
    ComputableIn.fst.comp ComputableIn.snd
  have hh : ComputableIn {charOracle A}
      fun q : BitString × BitString × BitString =>
        (fun (_ y : BitString) (x : BitString) => x) q.1 q.2.1 q.2.2 :=
    ComputableIn.snd.comp ComputableIn.snd
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_twoStage_le A
    (g := fun (_ : BitString) (y : BitString) (_ : ℕ) => y)
    (h := fun (_ y : BitString) x => x) hg hh
  refine ⟨c, fun x y z => ?_⟩
  have := hc z y x
  beta_reduce at this
  exact this

/-- **Chain rule with retained context**:
`K^A(x | z) ≤ K^A(y | z) + K^A(x | ⟨y, z⟩) + O(1)`. Blueprint node `split:chain-rule`. -/
theorem oraclePrefixComplexityNat_triangle_pair (A : Set ℕ) :
    ∃ c : ℕ, ∀ x y z : BitString,
      oraclePrefixComplexityNat A x z ≤
        oraclePrefixComplexityNat A y z + oraclePrefixComplexityNat A x (pairCode y z) + c := by
  have hg0 : ComputableIn {charOracle A} fun q : BitString × BitString × ℕ => (q.2.1, q.1) :=
    ComputableIn.pair (ComputableIn.fst.comp ComputableIn.snd) ComputableIn.fst
  have hg : ComputableIn {charOracle A}
      fun q : BitString × BitString × ℕ =>
        (fun (z y : BitString) (_ : ℕ) => pairCode y z) q.1 q.2.1 q.2.2 :=
    (pairCode_computable.computableIn.comp hg0).of_eq fun _ => rfl
  have hh : ComputableIn {charOracle A}
      fun q : BitString × BitString × BitString =>
        (fun (_ y : BitString) (x : BitString) => x) q.1 q.2.1 q.2.2 :=
    ComputableIn.snd.comp ComputableIn.snd
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_twoStage_le A
    (g := fun (z y : BitString) (_ : ℕ) => pairCode y z) (h := fun (_ y : BitString) x => x) hg hh
  refine ⟨c, fun x y z => ?_⟩
  have := hc z y x
  beta_reduce at this
  exact this

/-- **Coding direction of symmetry of information, conditional form**:
`K^A(⟨y, x⟩ | z) ≤ K^A(y | z) + K^A(x | y, K^A(y | z)) + O(1)`, where the second-stage context
is `prefixComplexityContext y (K^A(y | z)) = pairCode y (natCode (K^A(y | z)))`.
Blueprint node `split:chain-rule`. -/
theorem oraclePrefixComplexityNat_pair_le_cond_context (A : Set ℕ) :
    ∃ c : ℕ, ∀ y x z : BitString,
      oraclePrefixComplexityNat A (pairCode y x) z ≤
        oraclePrefixComplexityNat A y z +
          oraclePrefixComplexityNat A x
            (prefixComplexityContext y (oraclePrefixComplexityNat A y z)) + c := by
  have hg : ComputableIn {charOracle A}
      fun q : BitString × BitString × ℕ =>
        (fun (_ y : BitString) (n : ℕ) => prefixComplexityContext y n) q.1 q.2.1 q.2.2 :=
    prefixComplexityContext_computable.computableIn.comp ComputableIn.snd
  have hh : ComputableIn {charOracle A}
      fun q : BitString × BitString × BitString =>
        (fun (_ y : BitString) (x : BitString) => pairCode y x) q.1 q.2.1 q.2.2 :=
    pairCode_computable.computableIn.comp ComputableIn.snd
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_twoStage_le A
    (g := fun (_ y : BitString) (n : ℕ) => prefixComplexityContext y n)
    (h := fun (_ y : BitString) x => pairCode y x) hg hh
  refine ⟨c, fun y x z => ?_⟩
  have := hc z y x
  beta_reduce at this
  exact this

/-- **Coding direction of symmetry of information**:
`K^A(⟨y, x⟩) ≤ K^A(y) + K^A(x | y, K^A(y)) + O(1)`. Blueprint node `split:chain-rule`. -/
theorem oracleComplexity_pair_le_cond_context (A : Set ℕ) :
    ∃ c : ℕ, ∀ y x : BitString,
      oracleComplexity A (pairCode y x) ≤
        oracleComplexity A y +
          oraclePrefixComplexityNat A x (prefixComplexityContext y (oracleComplexity A y)) + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_pair_le_cond_context A
  exact ⟨c, fun y x => hc y x []⟩

/-- **Conditional concatenation**: `K^A(⟨y, x⟩ | z) ≤ K^A(y | z) + K^A(x | z) + O(1)`.
Blueprint node `split:chain-rule`. -/
theorem oraclePrefixComplexityNat_pair_le_add (A : Set ℕ) :
    ∃ c : ℕ, ∀ y x z : BitString,
      oraclePrefixComplexityNat A (pairCode y x) z ≤
        oraclePrefixComplexityNat A y z + oraclePrefixComplexityNat A x z + c := by
  have hg : ComputableIn {charOracle A}
      fun q : BitString × BitString × ℕ =>
        (fun (z : BitString) (_ : BitString) (_ : ℕ) => z) q.1 q.2.1 q.2.2 :=
    ComputableIn.fst
  have hh : ComputableIn {charOracle A}
      fun q : BitString × BitString × BitString =>
        (fun (_ y : BitString) (x : BitString) => pairCode y x) q.1 q.2.1 q.2.2 :=
    pairCode_computable.computableIn.comp ComputableIn.snd
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_twoStage_le A
    (g := fun (z : BitString) (_ : BitString) (_ : ℕ) => z)
    (h := fun (_ y : BitString) x => pairCode y x) hg hh
  refine ⟨c, fun y x z => ?_⟩
  have := hc z y x
  beta_reduce at this
  exact this

/-! ### Recoding -/

/-- **Recoding the condition.** If `f` is a relative partial operation and `z ∈ f y`, then
`K^A(x | y) ≤ K^A(x | z) + O(1)`: the machine first applies `f` to its context.
Blueprint node `split:recoding`. -/
theorem oraclePrefixComplexityNat_cond_le_of_partrecIn (A : Set ℕ) (f : BitString →. BitString)
    (hf : PartrecIn {charOracle A} f) :
    ∃ c : ℕ, ∀ x y z : BitString, z ∈ f y →
      oraclePrefixComplexityNat A x y ≤ oraclePrefixComplexityNat A x z + c := by
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec A
  set U := optimalOraclePrefix A with hUdef
  let D : Map := fun pr => (f pr.2).bind fun z => U (pr.1, z)
  have hD : IsDecompressorIn (charOracle A) D := by
    rw [isDecompressorIn_iff_partrecIn] at hUd ⊢
    exact (hf.comp ComputableIn.snd).bind
      (hUd.comp (ComputableIn.pair (ComputableIn.fst.comp ComputableIn.fst) ComputableIn.snd))
  have hDp : IsPrefixMachine D := by
    intro y p hp q hq hpre
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hq
    obtain ⟨z, hz, ha'⟩ := Part.mem_bind_iff.mp ha
    obtain ⟨z', hz', hb'⟩ := Part.mem_bind_iff.mp hb
    have hzz : z = z' := Part.mem_unique hz hz'
    subst hzz
    exact hUp.eq_of_prefix ha' hb' hpre
  obtain ⟨c, hc⟩ := hopt D hD hDp
  refine ⟨c, fun x y z hz => ?_⟩
  obtain ⟨p, hp, hl⟩ := exists_program_oraclePrefix A x z
  have hprod : produces D p y x := Part.mem_bind_iff.mpr ⟨z, hz, hp⟩
  have hbound : KP U x y ≤ ((p.length + c : ℕ) : ENat) := by
    calc KP U x y ≤ KP D x y + (c : ENat) := hc x y
      _ ≤ (p.length : ENat) + (c : ENat) := by
          gcongr; exact KP_le_programLength_of_produces hprod
      _ = ((p.length + c : ℕ) : ENat) := by norm_cast
  have := oraclePrefixComplexityNat_le_of_KP_le hbound
  omega

/-- **Recoding the output.** If `f` is a relative partial operation and `z ∈ f x`, then
`K^A(z | y) ≤ K^A(x | y) + O(1)`. Blueprint node `split:recoding`. -/
theorem oraclePrefixComplexityNat_map_le_of_partrecIn (A : Set ℕ) (f : BitString →. BitString)
    (hf : PartrecIn {charOracle A} f) :
    ∃ c : ℕ, ∀ x y z : BitString, z ∈ f x →
      oraclePrefixComplexityNat A z y ≤ oraclePrefixComplexityNat A x y + c := by
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec A
  set U := optimalOraclePrefix A with hUdef
  let D : Map := fun pr => (U pr).bind f
  have hD : IsDecompressorIn (charOracle A) D := by
    rw [isDecompressorIn_iff_partrecIn] at hUd ⊢
    exact relative_closure_comp A U f hUd hf
  have hDp : IsPrefixMachine D := by
    intro y p hp q hq hpre
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hq
    obtain ⟨x, hx, -⟩ := Part.mem_bind_iff.mp ha
    obtain ⟨x', hx', -⟩ := Part.mem_bind_iff.mp hb
    exact hUp.eq_of_prefix hx hx' hpre
  obtain ⟨c, hc⟩ := hopt D hD hDp
  refine ⟨c, fun x y z hz => ?_⟩
  obtain ⟨p, hp, hl⟩ := exists_program_oraclePrefix A x y
  have hprod : produces D p y z := Part.mem_bind_iff.mpr ⟨x, hp, hz⟩
  have hbound : KP U z y ≤ ((p.length + c : ℕ) : ENat) := by
    calc KP U z y ≤ KP D z y + (c : ENat) := hc z y
      _ ≤ (p.length : ENat) + (c : ENat) := by
          gcongr; exact KP_le_programLength_of_produces hprod
      _ = ((p.length + c : ℕ) : ENat) := by norm_cast
  have := oraclePrefixComplexityNat_le_of_KP_le hbound
  omega

/-- **Post-processing with access to the context.** For an `A`-computable `F`,
`K^A(F y x | y) ≤ K^A(x | y) + O(1)`. Blueprint node `split:recoding`. -/
theorem oraclePrefixComplexityNat_map_cond_le (A : Set ℕ)
    (F : BitString → BitString → BitString)
    (hF : ComputableIn {charOracle A} fun q : BitString × BitString => F q.1 q.2) :
    ∃ c : ℕ, ∀ x y : BitString,
      oraclePrefixComplexityNat A (F y x) y ≤ oraclePrefixComplexityNat A x y + c := by
  obtain ⟨hUd, hUp, hopt⟩ := exists_optimalOraclePrefix_spec A
  set U := optimalOraclePrefix A with hUdef
  let D : Map := fun pr => (U pr).map fun x => F pr.2 x
  have hD : IsDecompressorIn (charOracle A) D := by
    rw [isDecompressorIn_iff_partrecIn] at hUd ⊢
    exact hUd.map (hF.comp (ComputableIn.pair (ComputableIn.snd.comp ComputableIn.fst)
      ComputableIn.snd))
  have hDp : IsPrefixMachine D := by
    intro y p hp q hq hpre
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hq
    obtain ⟨x, hx, -⟩ := (Part.mem_map_iff _).mp ha
    obtain ⟨x', hx', -⟩ := (Part.mem_map_iff _).mp hb
    exact hUp.eq_of_prefix hx hx' hpre
  obtain ⟨c, hc⟩ := hopt D hD hDp
  refine ⟨c, fun x y => ?_⟩
  obtain ⟨p, hp, hl⟩ := exists_program_oraclePrefix A x y
  have hprod : produces D p y (F y x) := (Part.mem_map_iff _).mpr ⟨x, hp, rfl⟩
  have hbound : KP U (F y x) y ≤ ((p.length + c : ℕ) : ENat) := by
    calc KP U (F y x) y ≤ KP D (F y x) y + (c : ENat) := hc (F y x) y
      _ ≤ (p.length : ENat) + (c : ENat) := by
          gcongr; exact KP_le_programLength_of_produces hprod
      _ = ((p.length + c : ℕ) : ENat) := by norm_cast
  have := oraclePrefixComplexityNat_le_of_KP_le hbound
  omega

/-- **Recoding the condition by a total `A`-computable map**: `K(x | y) ≤ K(x | f y) + O(1)`.
Blueprint node `split:recoding`. -/
theorem oraclePrefixComplexityNat_cond_le_of_computableIn (A : Set ℕ) (f : BitString → BitString)
    (hf : ComputableIn {charOracle A} f) :
    ∃ c : ℕ, ∀ x y : BitString,
      oraclePrefixComplexityNat A x y ≤ oraclePrefixComplexityNat A x (f y) + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_cond_le_of_partrecIn A _ hf.partrecIn
  exact ⟨c, fun x y => hc x y (f y) (Part.mem_some _)⟩

/-- **Recoding the output by a total `A`-computable map**: `K(f x | y) ≤ K(x | y) + O(1)`.
Blueprint node `split:recoding`. -/
theorem oraclePrefixComplexityNat_map_le_of_computableIn (A : Set ℕ) (f : BitString → BitString)
    (hf : ComputableIn {charOracle A} f) :
    ∃ c : ℕ, ∀ x y : BitString,
      oraclePrefixComplexityNat A (f x) y ≤ oraclePrefixComplexityNat A x y + c := by
  obtain ⟨c, hc⟩ := oraclePrefixComplexityNat_map_le_of_partrecIn A _ hf.partrecIn
  exact ⟨c, fun x y => hc x y (f x) (Part.mem_some _)⟩

end Kolmogorov.PointToSet
