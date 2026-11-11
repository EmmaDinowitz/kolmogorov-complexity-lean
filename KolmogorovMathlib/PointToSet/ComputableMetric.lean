/-
Copyright (c) 2024 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import KolmogorovMathlib.PointToSet.ComputableMetric.Presentation
import KolmogorovMathlib.PointToSet.ComputableMetric.StaticDimensions
import KolmogorovMathlib.PointToSet.ComputableMetric.DimensionAlongScales
import KolmogorovMathlib.PointToSet.ComputableMetric.Points
import KolmogorovMathlib.PointToSet.ComputableMetric.CeOpen
import KolmogorovMathlib.PointToSet.ComputableMetric.Compact
import KolmogorovMathlib.PointToSet.ComputableMetric.Represented

/-!
# Fixed metric presentations, represented maps and static point dimensions

This directory sets up the effective framework in which points of a complete separable metric
space are measured by Kolmogorov complexity. A `Presentation` fixes a dense sequence of ideal
points independently of every oracle. Its density already implies nonemptiness and
separability; completeness is stored explicitly. Continuous dynamics and the finite family of
potentials are parameters of admissibility, so that one presentation serves different
dynamical data.

* `ComputableMetric.Presentation`: presentations, Cauchy names, represented maps (enumerable
  relations between rational basic balls) and their composition and uniform evaluation.
* `ComputableMetric.StaticDimensions`: the existence of an admissible base oracle for which the
  metric table, the map and the potentials are simultaneously computable
  (`exists_admissible_base`), precision complexity, and the static point dimensions.
* `ComputableMetric.DimensionAlongScales`: invariance of the static point dimensions under the
  choice of scales and of presentation.
* `ComputableMetric.Points`: relatively computable points and the strict distance certificates
  (membership in a basic ball, rational lower bounds on distances) that every effective search
  semidecides from uniformly computable names.
* `ComputableMetric.CeOpen`: relatively c.e. open sets and families, their closure under
  unions, reindexing and (above the metric table) intersections, and coded basic balls inside
  open sets.
* `ComputableMetric.Compact`: effective compactness as semidecidable containment in finite
  unions of basic balls.
* `ComputableMetric.Represented`: families of maps represented uniformly in a primcodable index
  and maps represented on a subset, with their evaluation and pullback lemmas.

All point dimensions live in `ENNReal` and use positive radii tending to zero. Computability of
the presentation is a hypothesis for algorithms, not part of the definition of complexity. The
dynamical quantities in `Dynamics`, the oracle comparisons in `Order` and every point-to-set
principle are formulated relative to a presentation of this kind.
-/
