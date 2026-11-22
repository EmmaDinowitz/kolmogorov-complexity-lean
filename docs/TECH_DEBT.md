# Technical debt and clean-up record

Living record of the clean-up work owed on the fork `EmmaDinowitz/kolmogorov-complexity-lean`
(branches `measure-chapter`, `van-lambalgen`, `ergodic`, `brin-katok`). Updated periodically
(about every ten user messages in the working session). Items are grouped by kind; each says
where it is, why it is debt, and what clearing it takes. Review of blueprint nodes (the
"Reviewed" columns) is the user's work and is not listed here.

Last updated: 2026-11-22 (branch `ergodic`, after the port of the ergodic chapter).

## 1. Branches, pushes and merges

| Item | State | To clear |
|---|---|---|
| `ergodic` (off `van-lambalgen`) | Holds the ergodic chapter and the completed Measure chapter, ported from the Formalization working tree (branch `ccr-359f2ff1-syi7ip` there, vendored range `105f7b8..8732de7`), which the user declared canonical on 2026-11-22. Builds (10,759 jobs, no warnings), no `sorry`, 137 headline theorems on standard axioms | Pushed to the fork on 2026-11-22 after all per-change gates passed |
| `brin-katok` (off `van-lambalgen`) | Local only, superseded: its KS library (`ks:*`), Birkhoff backport, Remarks 6.9 and 3.4(b), Proposition 7.10(i) and Example 5.5 re-prove, under other names, what the ported chapter already has | Compare with `ergodic` by declaration and statement, report to the user, keep only what `ergodic` lacks, then retire the branch |
| Stacked, unmerged branches | `ergodic` ⊃ `van-lambalgen` (pushed, `ef28bae`) ⊃ `measure-chapter` (`cedfa17`); merge of `van-lambalgen` into `measure-chapter` is on hold by the user's decision | Decide merge order (or fold into the reorganization) |
| `ergodic` lacks `geodesic-interface` | Formalization `main` pins the fork's `geodesic-interface` branch (`d86fb81`), which has neither van Lambalgen nor the ergodic chapter | Merge or rebase when the Formalization repository is to use this work |
| Private objects in this clone | The local refs `refs/cloud/*` pin commits fetched from the private Formalization repository; they are not ancestors of any branch | Never push them; delete the refs once `ergodic` is pushed and verified |
| Stale worktree for `measure-chapter` | `C:\Users\emmad\code\kolmogorov-measure` is at `cedfa17` (11 `sorry`s there, none on `ergodic`) | Fast-forward or retire once merges are decided |
| Worktree name mismatch | Branch `ergodic` is checked out in the worktree `kolmogorov-vanlambalgen` | Rename/move the worktree, or recreate per branch |
| The ergodic chapter's history | Kept only on `archive/ccr-359f2ff1-syi7ip` of the Formalization repository; `ergodic` has it as one commit | Nothing, unless the history is wanted on the fork |

## 2. Only on `brin-katok` (disappears if that branch is retired)

| Item | Where | Note |
|---|---|---|
| Backport of Mathlib's maximal and pointwise ergodic theorems (PRs #34031 and #42078, commit `ebc0f703f74b`) with a compatibility layer and a global `@[fun_prop]` attribute | `KolmogorovMathlib/MathlibBackport/` | The ported chapter has its own Birkhoff theorem (`KolmogorovMathlib/Ergodic/`); the backport is needed only if the comparison finds a use for it |
| Second KS-entropy library | `PointToSet/Measure/KSEntropy/` (`ks:*` nodes) | Duplicates `Kolmogorov.Ergodic.ksEntropy` and its API |
| Second proofs of Example 5.5, Remarks 6.9 and 3.4(b), Proposition 7.10(i) | `Measure/RandomNonAtom/`, `RemarksRates.lean`, `RemarksShift.lean`, `ShiftGeneric/BlockCoding.lean` | Example 5.5 there has an existential presentation; the ported one uses the standard presentation |

## 3. Duplicated or misplaced helpers (on `ergodic`)

| Helper | Where | Duplicate of / better home |
|---|---|---|
| Two computable presentations of Cantor space | `Measure/Ergodic/CantorPresentation.lean` (ported) and the product/itinerary machinery of `AlgorithmicRandomness/VanLambalgen/Metric/` | Check whether the transfer `mem_randomPoints_iff_itinerary` can replace hand-made Cantor-space arguments, or the reverse |

## 4. Documentation

| Item | Where | To clear |
|---|---|---|
| Three blueprints with different conventions | `docs/BLUEPRINT.md` (`vl`, `vlm`), `docs/entropy_noninvariant_blueprint.md` (`meas`), `docs/ml_random_orbit_complexity_blueprint.md` (`erg`) | Consolidate in the reorganization |
| `scripts/headline_theorems.txt` and `scripts/kernel_check.sh` refer to `notes/lean_translation.pdf`, which is not in this repository | `scripts/` | Add the note or correct the reference |
| `headline_theorems.txt` does not list the van Lambalgen results | `scripts/headline_theorems.txt` | Add the `vl`/`vlm` main theorems (they were checked separately on 2026-11-22) |
| `docs/design.md`, `docs/RESULTS.md` | Updated by the port for the Measure and ergodic chapters; no entry yet for the port itself | Add a dated entry |

## 5. Code-quality follow-ups

| Item | Where | To clear |
|---|---|---|
| Allow-list rows added for the mechanical-cut gate (2026-11-22) | Seven statements of the paper (Theorem 7.5(b), Remark 6.7 twice, Remark 7.11, the strictness statement of section 4.4, Proposition 7.6(i), `blockPattern_of_mem`) are allow-listed with reasons in `docs/history/cut_quality_allow.tsv`; six one-line wrapper lemmas were inlined. The gate now passes (0 unlisted) | User may review the seven reasons |
| Long proofs (> 120 lines) | `isComputableCantorMeasureIn_map` (286, `VanLambalgen/Metric/Transfer.lean`), `exists_isAlmostDecidableBasisIn` (134, `Metric/Basis.lean`); the ported chapter has not been surveyed | Split into lemmas in a clean-up pass; survey the ported files |
| Agent-written proofs in general | van Lambalgen phases, the ported chapter | One style pass before anything is published |

## 6. Remaining `sorry`s

None on `ergodic` (sorry scan of the whole tree, 2026-11-22).

## 7. Environment and tooling (Windows machine)

| Item | State | To clear |
|---|---|---|
| Lock wrapper | Now at `C:\Users\emmad\code\tools\leanlock.py` (lock file next to it). The copy in the session scratchpad vanished on 2026-11-21 and is a stub pointing to the new place; the `python3` shim that was beside it is gone | Use the real interpreter path (`...\Python313\python.exe`) with `PYTHONUTF8=1`; a shim is not needed |
| Out-of-memory failures during full builds | Two full builds each lost one or two modules to `std::bad_alloc` / "failed to read file ….olean"; a rerun finishes them | Rerun on that symptom only; keep one Lean process machine-wide |
| Dependencies via a junction | `.lake/packages` is a junction to the `kqw` checkout's packages; `.lake/build` was copied from an older build | Fresh clone + `lake exe cache get` during the reorganization |
| `scripts/audit.sh` does not pass on Windows on the clean base | Pre-existing failures: forbidden scan (Geodesic `maxHeartbeats` allow-list), `gen_deprecated`, file-size gate (it calls `python3`, which is the Store stub here; by hand, the only files over 1,000 lines are upstream ones), `cut_quality` | Fix upstream gates or allow-lists; meanwhile the per-change gates are run individually |

## 8. Deferred design choices (not debt, recorded so they are not lost)

* van Lambalgen: the blind (`μ` arbitrary) version on metric spaces; relativizing "random relative
  to `x`" by uniform tests instead of a Cauchy name.
* Lyapunov paper (v45): the reorganized proof is sketched in
  `C:\Users\emmad\code\lyapunov-paper\L0_reorganized_skeleton.tex`; open items are marked there
  (the extended joint lemma, specification inside basic sets, ergodicity of the time step,
  whether `α_{k+1} ≥ c_k α_k` is needed). Planned Lean home: branch `lyapunov` off `ergodic`,
  `PointToSet/Interleaving/` (`il:*`) and `PointToSet/LyapunovDimension/` (`lyap:*`).
