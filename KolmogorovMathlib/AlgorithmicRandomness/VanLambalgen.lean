/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Defs
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Join
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Halves
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Directions
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.MainResults

/-!
# The van Lambalgen theorem

A pair of sequences, encoded by interleaving, is random for a product measure exactly when its
first coordinate is random and its second is random relative to the first (blueprint
`docs/BLUEPRINT.md`, nodes `vl:*`).

* `Defs` — the interleaving `cantorJoin` and the joined product measure `joinMeasure`.
* `Join` — the oracle and the total mass of an interleaving, the uniform case, the swap.
* `Halves` — the even and odd halves of sequences and strings, joint sets `{z ⊕ y | y ∈ T z}`
  and their joined product measure (Fubini).
* `OracleUniform` — families of open sets enumerated uniformly in an oracle sequence: the use
  principle and trimming uniformly in the oracle.
* `Directions` — the three implications, each with the hypotheses it uses.
* `MainResults` — the theorem, its symmetric and mutual forms, the textbook uniform case and
  non-vacuousness.
-/
