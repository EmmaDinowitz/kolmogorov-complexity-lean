/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.Basic
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.UsePrinciple
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.OracleUniform.Trim

/-!
# Families of open sets enumerated uniformly in an oracle sequence

The two hard directions of the van Lambalgen theorem (blueprint nodes `vl:snd`, `vl:converse`)
handle families of open sets `T z n` that are effectively open relative to `A ⊕ z`, uniformly in
the oracle sequence `z`. This directory develops them (blueprint nodes `vl:oracle-uniform`,
`vl:sections`, `vl:use-principle`, `vl:uniform-trim`, `vl:discard`).

* `Basic` — oracle-uniform listings `g` computable relative to `A` and their families
  `uniformFamily g z n`; joint sets `{z ⊕ y | y ∈ T z n}` are effectively open relative to `A`;
  the family at `x` is effectively open relative to `A ⊕ x`; sections of an effectively open set.
* `UsePrinciple` — every family effectively open relative to `A ⊕ x` is the value at `x` of an
  oracle-uniform family relative to `A`.
* `Trim` — trimming uniformly in the oracle to `ν`-measure at most `2^{-L}`, and the effectively
  open set of oracles at which the trimming discards something.
-/
