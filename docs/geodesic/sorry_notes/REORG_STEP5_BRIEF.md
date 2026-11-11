# Brief for reorganization step 5 — `OrbitDatum` (Layer 3 abstraction), chapters D → H

Repository: /home/user/alexeymilovanov/kolmogorov-complexity-lean (`export PATH="$HOME/.elan/bin:$PATH"`).
Blueprint: docs/geodesic/computability_reorg_blueprint.md Section 4 ("Geodesic/OrbitData.lean") and
step 5 of Section 6. Log: docs/geodesic/sorry_notes/REORG_LOG.md (steps 0–4 done).
Backup before starting: copy `KolmogorovMathlib/PointToSet/Geodesic` to /home/user/backup_step5/.

This is the only step that changes statement shapes. Scope is deliberately bounded; what is
*not* done is recorded in the log (see "Deferred").

## New file `KolmogorovMathlib/PointToSet/Geodesic/OrbitData.lean`

Imports EffectiveData.lean (and whatever the moved lemmas need). Namespace `Kolmogorov.PointToSet`.

```
/-- An orbit datum for `x`: an ideal index whose orbit under `T` shadows the orbit of `x` at
`order` observed times within tolerance `tol`. -/
structure OrbitDatum (P : Presentation X) (T : X → X) (x : X) where
  idx : ℕ
  order : ℕ
  tol : ℝ
  mem : P.ι idx ∈ bowenBall T order x tol
```
(`tol : ℝ`, not `ℚ`: every tolerance on the main chain is a real `min ε (r / 8)`; the datum is a
proof object, never a program input.) With:

* `OrbitDatum.ofMem` (constructor from a membership), `OrbitDatum.mem_of_le` (weaken `tol`,
  lower `order` via `bowenBall_subset_of_le`/order monotonicity already in the library).
* `OrbitDatum.names` / `OrbitDatum.names_backward`: the current
  `EffectiveGeodesicData.orbit_approximants(_backward)` restated for `d : OrbitDatum P G.f x`
  with `d.order = n + 1`: names of `G.φ q (P.ι d.idx)` computable uniformly in `(q, p)` and within
  `G.L * d.tol` of `G.φ q x` for `0 ≤ q ≤ n`. The old theorems stay as one-line corollaries
  (their call sites in D are then switched to the datum form only if that is a local change).
* `OrbitDatum.abs_birkhoff_sub_le` (+ backward): the quadrature bounds
  `abs_birkhoff_uPlus_sub_le`/`uMinus` (PlaqueNeighborhoods.lean) restated through a datum.
* `OrbitDatum.scalePlus` / `scaleMinus`: `exists_computable_scalePlus/Minus` restated: the
  computable `Rp : ℕ × ℕ → ℚ` evaluated at `(d.idx, T)` brackets `G.scalePlus ρ T x`.
* `orbitComplexityNat_le_idx (d : OrbitDatum P T x) : orbitComplexityNat P T A x d.order d.tol ≤
  oracleNatComplexity A d.idx` and
  `orbitComplexityNat_eq_iInf_orbitDatum (hT : Continuous T) (hn) (hε : 0 < ε) :
  orbitComplexityNat P T A x n ε = ⨅ d : {d : OrbitDatum P T x // d.order = n ∧ d.tol = ε},
  oracleNatComplexity A d.1.idx` (from `orbitComplexityNat_attained` and `orbitComplexityNat_le`
  in FlowInterface.lean; `ℕ` has `InfSet`, use `le_antisymm` with `le_ciInf`/`ciInf_le` or the
  `Nat.sInf` API, whichever closes).

## Restatements (hypotheses only; program input types unchanged)

In `bracket_approx_forward/backward`, `net_approx` (BracketApprox.lean),
`effective_neighborhoods` (PlaqueNeighborhoods.lean) and `section_reconstruction`
(SectionReconstruction.lean), replace each pair

```
∀ ip im : ℕ, P.ι ip ∈ bowenBall G.f (Tp + 1) x (min ε (r / 8)) →
  P.ι im ∈ bowenBall G.finv (Tm + 1) x (min ε (r / 8)) → … (… ip, im …)
```
by
```
∀ (dp : OrbitDatum P G.f x) (dm : OrbitDatum P G.finv x),
  dp.order = Tp + 1 → dp.tol ≤ min ε (r / 8) → dm.order = Tm + 1 → dm.tol ≤ min ε (r / 8) →
  … (… dp.idx, dm.idx …)
```
(and the one-sided analogue in `bracket_approx_forward/backward`). Everything else in these
statements is unchanged. `orbit_to_location` and its corollaries (OrbitToLocation.lean) keep their
statements exactly (Chapter I consumes them) and construct the data with `OrbitDatum.ofMem`.
Chapter D's decoders keep their `(kp, r, i, T, kq, p)` inputs and `shadowSet` hypotheses.

Do it chapter by chapter in the order OrbitData → D (use of names) → E → F → G → H, with
`lake build KolmogorovMathlib.PointToSet.Geodesic.UpperBound` after each chapter
(logs reorg_build5_<X>.log in docs/geodesic/sorry_notes/).

## Deferred (record in the log, do not do)

* The `LocalizationCode` record for program inputs: a `Primcodable` instance via an `Equiv` to the
  product is routine, but every `PartrecIn` projection proof in D–G would have to be re-derived for
  no mathematical gain. Keep nested products.
* Making `OrbitDatum` a program input.

## Gates and logging

Build gate exit 0, no errors, no new `sorry` (the two in EffectiveData `uPlus_represented`/
`uMinus_represented` are pre-existing). Add `Geodesic.OrbitData` nowhere yet (the Geodesic modules
are not listed in `KolmogorovMathlib.lean` until step 7). Docstrings on every declaration, lines
≤ 100, new file < 1,000 lines, `python3 -B scripts/docstring_coverage.py --check`,
`python3 -B scripts/check_headers.py --by-name`, `python3 -B scripts/import_hygiene.py --check`.
Log: table row for step 5 and a "Step 5 notes" section with the final statements of every
restated theorem, the new declarations, and line counts. Never commit or push.
