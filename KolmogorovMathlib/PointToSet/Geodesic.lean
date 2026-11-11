/-
Copyright (c) 2026 Emma Dinowitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emma Dinowitz
-/
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface
import KolmogorovMathlib.PointToSet.Geodesic.FlowInterface.OrbitExtension
import KolmogorovMathlib.PointToSet.Geodesic.GeometricData
import KolmogorovMathlib.PointToSet.Geodesic.EffectiveData
import KolmogorovMathlib.PointToSet.Geodesic.OrbitData
import KolmogorovMathlib.PointToSet.Geodesic.Localization
import KolmogorovMathlib.PointToSet.Geodesic.BracketApprox.Geometry
import KolmogorovMathlib.PointToSet.Geodesic.BracketApprox
import KolmogorovMathlib.PointToSet.Geodesic.PlaqueNeighborhoods
import KolmogorovMathlib.PointToSet.Geodesic.SectionReconstruction
import KolmogorovMathlib.PointToSet.Geodesic.Surface.JacobiSolutions
import KolmogorovMathlib.PointToSet.Geodesic.Surface.Riccati
import KolmogorovMathlib.PointToSet.Geodesic.OrbitToLocation
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.Returns
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.PrecisionChain
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.SectionPoint
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound.Mixed
import KolmogorovMathlib.PointToSet.Geodesic.UpperBound

/-!
# Upper bounds for the dimensions of geodesic-flow orbits (geodesic blueprint, Chapters A–I)

This directory formalizes the controlled-return upper bound of `geodesic_upper_bound_blueprint.md`:
for a flow with local product structure and uniformly continuous unit potentials `u^±`, the
static point dimensions of a point with controlled regular returns and positive rates are bounded
by one plus the forward and backward Barreira–Schmeling dimensions (`main_pointwise`), and the
same bound holds for sets (`main_set`). The effective ingredients come from the layers
`Oracle/`, `ComputableMetric/` and `EffectiveLocalization/`; this directory holds the geometry
and the programs specific to the flow.

* `Geodesic.FlowInterface`: the flow-to-map interface `FlowData` (time-one map and its inverse,
  Bowen balls against continuous orbits, unit potentials), finite orbit complexity and the
  denominator swap; `Geodesic.FlowInterface.OrbitExtension`: padding an orbit description by
  itinerary data (Chapter A).
* `Geodesic.GeometricData`: the standing geometric data `GeodesicReconstructionData` (leaves,
  plaques, compact plaques, brackets, flow boxes) (Chapter B).
* `Geodesic.EffectiveData`: the effective data `EffectiveGeodesicData` over a base oracle and
  its existence (Chapter C).
* `Geodesic.OrbitData`: orbit data `OrbitDatum`, their uniform names, the quadrature bounds and
  the computable integral scales `scalePlus`, `scaleMinus`.
* `Geodesic.Localization`: shadow sets and the localization decoders (Chapter D).
* `Geodesic.BracketApprox.Geometry`, `Geodesic.BracketApprox`: local products from finite orbit
  data, geometry and programs, and the approximation on a marked net (Chapter E).
* `Geodesic.PlaqueNeighborhoods`: effective neighborhoods of the local plaques at the integral
  scales (Chapter F).
* `Geodesic.SectionReconstruction`: reconstruction of the section point from the two
  neighborhoods and the flow-box data (Chapter G).
* `Geodesic.OrbitToLocation`: the orbit-to-location estimate (Chapter H).
* `Geodesic.UpperBound.Returns`, `.PrecisionChain`, `.SectionPoint`, `.Mixed`,
  `Geodesic.UpperBound`: controlled returns, stopping times, the precision chain, the two
  section-point bounds and the main theorems (Chapter I).
-/
