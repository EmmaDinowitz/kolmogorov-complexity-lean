/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Countable.Defs
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Countable.Split

/-!
# Countable products

The infinite join of a sequence of sequences and the countable product measure it carries, and the
reduction of the countable van Lambalgen theorem to the binary one (blueprint `docs/BLUEPRINT.md`,
nodes `vl:pi-*`).

* `Defs` — `cantorPiJoin`, `piJoinMeasure`, `cantorPiJoinExcept`, `cantorPiJoinBelow`,
  `skipIndex`, `cantorPiJoinSkip`.
* `Split` — splitting one coordinate off an infinite join, and the oracles of the other and of the
  earlier coordinates.
-/
