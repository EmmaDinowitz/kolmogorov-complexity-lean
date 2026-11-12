/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs
import KolmogorovMathlib.AlgorithmicRandomness.Trim

/-!
# Definitions used in the proof of the van Lambalgen theorem

These definitions appear in no main statement of the van Lambalgen chapter
(`VanLambalgen/MainResults.lean`); they are the objects the proofs work with.

* The two halves of a sequence and of a string, and the set `{z ⊕ y | y ∈ T z}` of a family of
  sets indexed by sequences (blueprint nodes `vl:halves`, `vl:joint-set`).
* Oracle-uniform families: families of open sets `T z n` indexed by an oracle sequence `z` and a
  level `n`, whose cylinders are listed by one function `g : BitString → ℕ → ℕ → Option BitString`
  computable relative to `A` (blueprint nodes `vl:oracle-uniform`, `vl:sections`).
* Trimming an oracle-uniform family uniformly in the oracle, and the set of oracles at which the
  trimming discards something (blueprint nodes `vl:uniform-trim`, `vl:discard`).

## Conventions

`cantorEvens w k = w (2k)` and `cantorOdds w k = w (2k+1)`, matching `cantorJoin`, which puts its
first argument on the even positions. For a string `ρ` of length `ℓ`, `evenBits ρ` has length
`⌈ℓ/2⌉` and `oddBits ρ` has length `⌊ℓ/2⌋`.

Oracles are sets of natural numbers queried through `charOracle`. In `uniformEnum g z n j` the
index `j` codes the pair `(k, i)` by `Nat.pair`: the string `g (cantorPrefix z k) n i` is
enumerated. No monotonicity of `g` in its string argument is required.

The trimmed family is listed by `trimUniform a g` at the level `Nat.pair n L`: `n` is the level of
the original family and `L` the trimming level. The finite-list helpers it is built from live in
the namespace `Kolmogorov.TrimUniform`; their entries at index `j` depend only on the first `j + 1`
entries of the enumeration at the oracle prefix `σ`.

## Main definitions

* `cantorEvens`, `cantorOdds`, `evenBits`, `oddBits` (blueprint node `vl:halves`).
* `jointSet` (blueprint node `vl:joint-set`).
* `IsOracleUniformIn`, `uniformEnum`, `uniformFamily` (blueprint node `vl:oracle-uniform`).
* `sectionEnum` (blueprint node `vl:sections`).
* `trimUniform` and the helpers `TrimUniform.localDisj`, `TrimUniform.localAccept`
  (blueprint node `vl:uniform-trim`).
* `discardSet` (blueprint node `vl:discard`).

Used by `VanLambalgen/Halves.lean`, `VanLambalgen/OracleUniform/`, `VanLambalgen/Directions/`,
`VanLambalgen/Join.lean` and `VanLambalgen/Countable/Split.lean`.
-/

namespace Kolmogorov

/-! ### Halves of sequences and strings -/

/-- The even half of a sequence: `cantorEvens w k = w (2k)`. Blueprint node `vl:halves`. -/
def cantorEvens (w : CantorSeq) : CantorSeq := fun k => w (2 * k)

/-- The odd half of a sequence: `cantorOdds w k = w (2k+1)`. Blueprint node `vl:halves`. -/
def cantorOdds (w : CantorSeq) : CantorSeq := fun k => w (2 * k + 1)

/-- The even half of a string: its entries at the positions `0, 2, 4, …`, a string of length
`⌈|ρ|/2⌉`. Blueprint node `vl:halves`. -/
def evenBits (ρ : BitString) : BitString :=
  (List.range ((ρ.length + 1) / 2)).map fun k => ρ.getD (2 * k) false

/-- The odd half of a string: its entries at the positions `1, 3, 5, …`, a string of length
`⌊|ρ|/2⌋`. Blueprint node `vl:halves`. -/
def oddBits (ρ : BitString) : BitString :=
  (List.range (ρ.length / 2)).map fun k => ρ.getD (2 * k + 1) false

/-- The set of interleavings `z ⊕ y` with `y ∈ T z`, written through the halves: a sequence `w`
belongs to it when `cantorOdds w ∈ T (cantorEvens w)`. For `T` constantly empty it is empty.
Blueprint node `vl:joint-set`. -/
def jointSet (T : CantorSeq → Set CantorSeq) : Set CantorSeq :=
  {w | cantorOdds w ∈ T (cantorEvens w)}

/-! ### Oracle-uniform families -/

/-- A function listing strings for every finite oracle prefix `σ`, level `n` and stage `i` is
oracle-uniform relative to `A` when it is computable relative to `A` as a function of the triple.
Blueprint node `vl:oracle-uniform`. -/
def IsOracleUniformIn (A : Set ℕ) (g : BitString → ℕ → ℕ → Option BitString) : Prop :=
  ComputableIn {charOracle A} fun p : BitString × ℕ × ℕ => g p.1 p.2.1 p.2.2

/-- The enumeration of the member of level `n` at the oracle sequence `z`: at the index coding
`(k, i)` it lists `g (cantorPrefix z k) n i`. Blueprint node `vl:oracle-uniform`. -/
def uniformEnum (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n : ℕ) :
    ℕ → Option BitString :=
  fun j => g (cantorPrefix z (Nat.unpair j).1) n (Nat.unpair j).2

/-- The member of level `n` at the oracle sequence `z` of the family listed by `g`: the union of
the cylinders `g σ n i` over the prefixes `σ` of `z`. It is empty when `g` lists nothing.
Blueprint node `vl:oracle-uniform`. -/
def uniformFamily (g : BitString → ℕ → ℕ → Option BitString) (z : CantorSeq) (n : ℕ) :
    Set CantorSeq :=
  ⋃ j, coverSet (uniformEnum g z n) j

/-- The oracle-uniform listing of the sections `{y | z ⊕ y ∈ W m}` of a set `W` listed by `f`:
for the oracle prefix `σ`, level `m` and stage `i` it lists `oddBits ρ` when `f m i = some ρ`
and `evenBits ρ = σ`, and nothing otherwise. Blueprint node `vl:sections`. -/
def sectionEnum (f : ℕ → ℕ → Option BitString) : BitString → ℕ → ℕ → Option BitString :=
  fun σ m i => (f m i).bind fun ρ => bif decide (evenBits ρ = σ) then some (oddBits ρ) else none

/-! ### Trimming uniformly in the oracle -/

namespace TrimUniform

/-- A finite list of optional strings read as an enumeration, empty beyond its length.
Blueprint node `vl:uniform-trim`. -/
def listEnum (l : List (Option BitString)) (i : ℕ) : Option BitString := l.getD i none

/-- The first `N` entries of the enumeration of level `n` at the oracle prefix `σ`.
Blueprint node `vl:uniform-trim`. -/
def prefixEnumList (g : BitString → ℕ → ℕ → Option BitString) (σ : BitString)
    (n N : ℕ) : List (Option BitString) :=
  (List.range N).map fun j => g (σ.take (Nat.unpair j).1) n (Nat.unpair j).2

/-- The first `N` entries of the disjointification of `prefixEnumList`.
Blueprint node `vl:uniform-trim`. -/
def disjList (g : BitString → ℕ → ℕ → Option BitString) (σ : BitString) (n N : ℕ) :
    List (Option BitString) :=
  (List.range N).map (disjEnum (listEnum (prefixEnumList g σ n N)))

/-- The first `N` trimming weights of `disjList`, at the trimming level `L`.
Blueprint node `vl:uniform-trim`. -/
def weightList (a : BitString → ℕ → ℕ) (g : BitString → ℕ → ℕ → Option BitString)
    (σ : BitString) (n L N : ℕ) : List ℕ :=
  (List.range N).map (trimWeight a (listEnum (disjList g σ n N)) L)

/-- The disjointified entry at index `j`, computed at the oracle prefix `σ`.
Blueprint node `vl:uniform-trim`. -/
def localDisj (g : BitString → ℕ → ℕ → Option BitString) (σ : BitString) (n j : ℕ) :
    Option BitString :=
  listEnum (disjList g σ n (j + 1)) j

/-- The trimming decision at index `j`, computed at the oracle prefix `σ`.
Blueprint node `vl:uniform-trim`. -/
def localAccept (a : BitString → ℕ → ℕ) (g : BitString → ℕ → ℕ → Option BitString)
    (σ : BitString) (n L j : ℕ) : Bool :=
  trimAccept (fun k => (weightList a g σ n L (j + 1)).getD k 0) j

end TrimUniform

open TrimUniform in
/-- The trimmed oracle-uniform listing at the level `Nat.pair n L`: at the oracle prefix `σ` and
index `j ≤ |σ|` it lists the `j`-th disjointified entry of level `n` if the trimming at level `L`
accepts it, and nothing otherwise; at indices `j > |σ|` it lists nothing.
Blueprint node `vl:uniform-trim`. -/
def trimUniform (a : BitString → ℕ → ℕ) (g : BitString → ℕ → ℕ → Option BitString) :
    BitString → ℕ → ℕ → Option BitString :=
  fun σ m j =>
    bif decide (j ≤ σ.length) && localAccept a g σ (Nat.unpair m).1 (Nat.unpair m).2 j then
      localDisj g σ (Nat.unpair m).1 j
    else none

/-- The oracles at which the trimming of level `n` at the trimming level `L` rejects some nonempty
entry of the disjointified enumeration. Blueprint node `vl:discard`. -/
def discardSet (a : BitString → ℕ → ℕ) (g : BitString → ℕ → ℕ → Option BitString)
    (n L : ℕ) : Set CantorSeq :=
  {z | ∃ j, disjEnum (uniformEnum g z n) j ≠ none ∧
    trimAccept (trimWeight a (disjEnum (uniformEnum g z n)) L) j = false}

end Kolmogorov
