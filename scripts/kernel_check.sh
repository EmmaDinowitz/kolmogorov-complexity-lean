#!/usr/bin/env bash
# Independent kernel check of KolmogorovMathlib.
#
# What it does (each stage can be skipped, see --help):
#   1. build      `lake build KolmogorovMathlib` (so the .olean files match the sources).
#   2. scan       source scan for `sorry`, `admit`, `axiom`, `native_decide`,
#                 `implemented_by`, `@[extern]`, `unsafe`, `debug.*` options
#                 (scripts/forbidden_scan.py, comment- and string-aware).
#   3. axioms     `#print axioms` for every theorem in scripts/headline_theorems.txt;
#                 fails unless each uses only propext, Classical.choice, Quot.sound.
#   4. replay     `leanchecker` (lean4checker, shipped with the toolchain) replays every
#                 declaration of each module in scope through Lean's kernel, against the
#                 environment of its imports. One module per process (all at once runs out
#                 of memory); `-j N` runs N in parallel.
#   5. export     `leanexport` writes the headline theorems and their full dependency
#                 closure (including Mathlib and Lean core) to a lean4export file, then
#                   a. `leanchecker --from-export` re-checks it with Lean's kernel starting
#                      from an EMPTY environment (nothing trusted from the .olean files);
#                   b. `nanoda_bin` (an independent type checker written in Rust, shipped
#                      with the toolchain) re-checks it from scratch with only
#                      propext / Classical.choice / Quot.sound permitted, and pretty-prints
#                      the headline statements as IT reads them (statements.txt): compare
#                      these with the statements in notes/lean_translation.pdf.
#
# lean4lean is also shipped with the toolchain, but this build can read neither the
# toolchain's .olean files ("incompatible header") nor export files, so it is not used.
#
# Usage: scripts/kernel_check.sh [--scope chapter|all] [-j N] [--out DIR]
#                                [--no-build] [--skip STAGE]...
#   --scope chapter  (default) modules under KolmogorovMathlib/PointToSet/Measure/,
#                    KolmogorovMathlib/Ergodic/ and KolmogorovMathlib/Trusted/ (about 100
#                    modules, ~15 min at -j 1).
#   --scope all      every module of KolmogorovMathlib (~1700 modules, hours).
#   STAGE is one of: scan axioms replay export.
# Exit status 0 iff every stage that ran passed. Logs and results go to --out
# (default .lake/kernel-check/).
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SCOPE=chapter; JOBS=1; OUT="$ROOT/.lake/kernel-check"; BUILD=1; SKIP=" "
while [ $# -gt 0 ]; do
  case "$1" in
    --scope) SCOPE="$2"; shift 2 ;;
    -j) JOBS="$2"; shift 2 ;;
    --out) OUT="$2"; shift 2 ;;
    --no-build) BUILD=0; shift ;;
    --skip) SKIP="$SKIP$2 "; shift 2 ;;
    -h|--help) sed -n '2,36p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
skipped() { case "$SKIP" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }

export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$OUT"
BIN="$(lean --print-prefix)/bin"
for t in leanchecker leanexport nanoda_bin; do
  [ -x "$BIN/$t" ] || { echo "missing $BIN/$t (toolchain $(cat lean-toolchain))" >&2; exit 2; }
done
ALLOWED='propext Classical.choice Quot.sound'
HEADLINES="$OUT/headlines.txt"
grep -v '^\s*#' scripts/headline_theorems.txt | grep . > "$HEADLINES"
STATUS=0
pass() { echo "PASS  $*"; }
fail() { echo "FAIL  $*"; STATUS=1; }

echo "== kernel check of $(basename "$ROOT") at $(git rev-parse --short HEAD 2>/dev/null)," \
  "toolchain $(cat lean-toolchain), scope $SCOPE, $(wc -l < "$HEADLINES") headline theorems"
echo "== pinned dependencies (lake-manifest.json):"
python3 -c 'import json; [print("   ", p["name"], p.get("rev","")[:12], p.get("url","")) for p in json.load(open("lake-manifest.json"))["packages"]]'

# 1. build
if [ $BUILD = 1 ]; then
  if lake build KolmogorovMathlib > "$OUT/build.log" 2>&1; then pass "build"; else fail "build (see $OUT/build.log)"; exit 1; fi
fi

# 2. source scan
if ! skipped scan; then
  if python3 scripts/forbidden_scan.py --mode forbidden KolmogorovMathlib > "$OUT/scan.log" 2>&1 \
     && python3 scripts/forbidden_scan.py --mode sorry KolmogorovMathlib >> "$OUT/scan.log" 2>&1; then
    pass "source scan (no sorry/axiom/native_decide/implemented_by/extern/unsafe)"
  else fail "source scan (see $OUT/scan.log)"; fi
fi

# 3. #print axioms for the headline theorems
if ! skipped axioms; then
  AX="$OUT/Axioms.lean"
  { echo "import KolmogorovMathlib"; sed 's/^/#print axioms /' "$HEADLINES"; } > "$AX"
  lake env lean "$AX" > "$OUT/axioms.log" 2>&1
  python3 - "$OUT/axioms.log" "$HEADLINES" "$ALLOWED" > "$OUT/axioms.txt" <<'EOF'
import re, sys
log = open(sys.argv[1]).read()
names = [l.strip() for l in open(sys.argv[2]) if l.strip()]
allowed = set(sys.argv[3].split())
bad = 0
for n in names:
    m = re.search(r"'" + re.escape(n) + r"' depends on axioms: \[([^\]]*)\]", log)
    if not m:
        m0 = re.search(r"'" + re.escape(n) + r"' does not depend on any axioms", log)
        if m0:
            print(f"OK    {n}: no axioms"); continue
        print(f"ERROR {n}: no #print axioms output"); bad += 1; continue
    axs = {a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()}
    extra = axs - allowed
    print(("OK    " if not extra else "BAD   ") + f"{n}: {sorted(axs)}")
    bad += bool(extra)
sys.exit(1 if bad else 0)
EOF
  if [ $? = 0 ]; then pass "axioms: every headline theorem uses only {$ALLOWED} ($OUT/axioms.txt)"
  else fail "axioms ($OUT/axioms.txt, $OUT/axioms.log)"; fi
fi

# 4. per-module kernel replay with leanchecker
if ! skipped replay; then
  case "$SCOPE" in
    chapter) find KolmogorovMathlib/PointToSet/Measure KolmogorovMathlib/Ergodic KolmogorovMathlib/Trusted -name '*.lean' ;;
    all) find KolmogorovMathlib -name '*.lean' ;;
    *) echo "bad scope $SCOPE" >&2; exit 2 ;;
  esac | sed 's/\.lean$//; s#/#.#g' | sort > "$OUT/modules.txt"
  : > "$OUT/replay.log"
  export OUT
  xargs -a "$OUT/modules.txt" -P "$JOBS" -I{} bash -c \
    'if lake env leanchecker "{}" > "$OUT/replay.{}.log" 2>&1; then echo "ok   {}"; else echo "FAIL {}"; fi' \
    >> "$OUT/replay.log"
  NMOD=$(wc -l < "$OUT/modules.txt"); NFAIL=$(grep -c '^FAIL' "$OUT/replay.log")
  if [ "$NFAIL" = 0 ] && [ "$(grep -c '^ok' "$OUT/replay.log")" = "$NMOD" ]; then
    pass "leanchecker replayed all $NMOD modules in scope '$SCOPE'"
  else fail "leanchecker: $NFAIL of $NMOD modules failed ($OUT/replay.log)"; fi
fi

# 5. export the headline closure; re-check from scratch with Lean's kernel and with nanoda
if ! skipped export; then
  EXP="$OUT/headlines.export"
  # shellcheck disable=SC2046
  if lake env leanexport KolmogorovMathlib -- $(cat "$HEADLINES") > "$EXP" 2> "$OUT/export.log"; then
    echo "      export: $(du -h "$EXP" | cut -f1)"
    if lake env leanchecker --from-export "$EXP" > "$OUT/fresh.log" 2>&1 \
       && grep -q 'accepts' "$OUT/fresh.log"; then
      pass "leanchecker --from-export: Lean kernel accepts the closure from an empty environment"
    else fail "leanchecker --from-export ($OUT/fresh.log)"; fi
    python3 - "$EXP" "$HEADLINES" "$OUT" <<'EOF'
import json, sys
exp, heads, out = sys.argv[1], sys.argv[2], sys.argv[3]
cfg = {
    "export_file_path": exp, "use_stdin": False,
    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "unpermitted_axiom_hard_error": False,
    "nat_extension": True, "string_extension": True,
    "pp_declars": [l.strip() for l in open(heads) if l.strip()],
    "pp_output_path": out + "/statements.txt", "pp_to_stdout": False,
    "pp_options": {"proofs": False, "indent": 2, "width": 100, "declar_sep": "\n\n"},
    "print_success_message": True,
}
json.dump(cfg, open(out + "/nanoda.json", "w"), indent=2)
EOF
    : > "$OUT/statements.txt"   # nanoda does not create its output file
    if "$BIN/nanoda_bin" "$OUT/nanoda.json" > "$OUT/nanoda.log" 2>&1 \
       && grep -q 'with no errors' "$OUT/nanoda.log"; then
      pass "nanoda: $(grep -o 'Checked [0-9]* declarations' "$OUT/nanoda.log") with no errors," \
        "only {$ALLOWED} permitted; statements in $OUT/statements.txt"
    else fail "nanoda ($OUT/nanoda.log)"; fi
  else fail "leanexport ($OUT/export.log)"; fi
fi

echo "== $( [ $STATUS = 0 ] && echo 'ALL STAGES PASSED' || echo 'SOME STAGES FAILED' )  (logs: $OUT)"
exit $STATUS
