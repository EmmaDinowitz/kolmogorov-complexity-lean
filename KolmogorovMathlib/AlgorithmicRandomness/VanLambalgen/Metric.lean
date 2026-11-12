/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Defs
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Transfer
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Oracle
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Basis
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.Product
import KolmogorovMathlib.AlgorithmicRandomness.VanLambalgen.Metric.MainResults

/-!
# The van Lambalgen theorem on presented metric spaces

The transfer of the Cantor-space theorem to presented metric spaces through almost decidable
bases and itineraries (Hoyrup–Rojas); blueprint `docs/BLUEPRINT.md`, nodes `vlm:*`.

* `Defs` — names as oracles, product presentations, almost decidable bases, itineraries.
* `Transfer` — itineraries preserve randomness; the image measure is computable.
* `Oracle` — at a random point the itinerary is the least degree of a name.
* `Basis` — existence of almost decidable bases.
* `Product` — products of presentations and of bases.
* `MainResults` — van Lambalgen's theorem on presented spaces.
-/
