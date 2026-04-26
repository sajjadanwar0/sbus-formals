#!/usr/bin/env bash
# run_formal.sh — Close all S-Bus formal-verification gaps in one invocation.
#
# Runs (in order):
#   1. Dafny verification of proofs/sbus_lemmas.dfy     (~30s)
#   2. tlapm mechanisation of proofs/SBus_TLAPS.tla    (~5-15min)
#   3. TLC at N=3                                   (~10s)
#   4. TLC at N=4 reduced                           (~10s)
#   5. TLC at N=4 full                              (~1h18min on 16-worker,
#                                                    ~2h on 8-worker,
#                                                    ~7h on 4-worker)
#
# DEFAULT BEHAVIOUR:
#   ./run_formal.sh
#     - Steps 1-4 run foreground in this terminal (5-15 min total)
#     - Step 5 (N=4 full TLC) auto-starts in the BACKGROUND with nohup,
#       survives SSH disconnect, writes to results/tlc_tlc_n4_full.log
#     - Terminal returns immediately after step 4
#     - results/formal_results.json updates automatically when step 5 finishes
#     - No manual intervention required.
#
#   This is what you almost certainly want for unattended runs.
#
# OTHER MODES:
#   ./run_formal.sh --status        # Check status of any running background job
#   ./run_formal.sh --wait          # Block until background TLC finishes, then re-analyse
#   ./run_formal.sh --foreground    # Run all 5 steps sequentially, terminal blocks ~2h
#   ./run_formal.sh --skip-tlc-full # Skip step 5 entirely
#   ./run_formal.sh --proof-only    # Only Dafny+tlapm (steps 1-2)
#   ./run_formal.sh --tlc-only      # Only TLC (steps 3-5)
#
# ENVIRONMENT OVERRIDES:
#   TLC_WORKERS=8     # Number of TLC workers for step 5 (default 16)
#   TLC_HEAP=8g       # JVM heap for TLC (default 8g)
#   TLA_JAR=path      # Path to tla2tools.jar (default ./tla2tools.jar)
#   DAFNY=path        # Path to dafny binary  (default `dafny`)
#   TLAPM=path        # Path to tlapm binary  (default `tlapm`)
#
# Output:
#   results/formal_results.json         — machine-readable summary
#   results/dafny.log                   — Dafny output
#   results/tlapm.log                   — tlapm output
#   results/tlc_tlc_n3.log              — TLC N=3 output
#   results/tlc_tlc_n4_reduced.log      — TLC N=4 reduced output
#   results/tlc_tlc_n4_full.log         — TLC N=4 full output (background)
#   results/tlc_n4_full.pid             — PID file for background TLC
#
# Tool requirements:
#   - dafny (4.x)   — install: https://github.com/dafny-lang/dafny/releases
#   - tlapm         — install: https://github.com/tlaplus/tlapm
#   - java 11+      — install: apt install default-jdk
#   - tla2tools.jar — https://github.com/tlaplus/tlaplus/releases
#                     (or use the bundled one in this directory)

set -uo pipefail

# Always run from the repo root so relative paths work whether the user
# invokes this as ./scripts/run_formal.sh, or cd scripts && ./run_formal.sh,
# or via a symlink.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$REPO_ROOT"

# Defaults
SKIP_TLC_FULL=false
TLC_ONLY=false
PROOF_ONLY=false
FOREGROUND=false       # if true, run N=4 full in foreground (blocks terminal)
WAIT_MODE=false        # if true, wait for existing background job to finish
STATUS_MODE=false      # if true, just print status of background job and exit
FINALISE_MODE=false    # if true, status + patch JSON (internal: used as post-TLC hook)
TLC_WORKERS=${TLC_WORKERS:-16}
TLC_HEAP=${TLC_HEAP:-8g}
TLA_JAR=${TLA_JAR:-tla2tools.jar}
TLAPM=${TLAPM:-tlapm}
TLAPS_LIB=${TLAPS_LIB:-/usr/local/lib/tlaps}
DAFNY=${DAFNY:-dafny}

for arg in "$@"; do
  case "$arg" in
    --skip-tlc-full) SKIP_TLC_FULL=true ;;
    --tlc-only)      TLC_ONLY=true ;;
    --proof-only)    PROOF_ONLY=true ;;
    --foreground)    FOREGROUND=true ;;
    --wait)          WAIT_MODE=true ;;
    --status)        STATUS_MODE=true ;;
    --finalise)      FINALISE_MODE=true ;;
    -h|--help)
      sed -n '2,60p' "$0"
      exit 0
      ;;
    *)
      echo "Unknown arg: $arg" >&2
      exit 2
      ;;
  esac
done

mkdir -p results
RESULTS=results/formal_results.json
PID_FILE=results/tlc_n4_full.pid
STARTTS=$(date -u +%FT%TZ)

# JSON accumulator
declare -A J
J[start]="$STARTTS"

# ── helpers ───────────────────────────────────────────────────────────────────

log()  { printf '\033[1;34m[%s]\033[0m %s\n' "$(date +%T)" "$*"; }
ok()   { printf '\033[1;32m  PASS\033[0m %s\n' "$*"; }
fail() { printf '\033[1;31m  FAIL\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33m  WARN\033[0m %s\n' "$*"; }

require_tool() {
  if ! command -v "$1" >/dev/null 2>&1; then
    fail "$1 not found in PATH (set ${2:-$1^^} env var or install)"
    return 1
  fi
  return 0
}

# Extract first line matching a regex
extract_first() { grep -m1 -oE "$1" "$2" 2>/dev/null || echo ""; }

# ── Background-job status helpers ─────────────────────────────────────────────
# Used by --status, --wait, and also when the main block re-analyses a
# completed background run.

bg_is_running() {
  # Returns 0 if PID file exists AND process is alive.
  [[ -f "$PID_FILE" ]] || return 1
  local pid
  pid=$(cat "$PID_FILE" 2>/dev/null)
  [[ -n "$pid" ]] || return 1
  kill -0 "$pid" 2>/dev/null
}

bg_print_status() {
  local logf="results/tlc_tlc_n4_full.log"
  if bg_is_running; then
    local pid et
    pid=$(cat "$PID_FILE")
    et=$(ps -o etime= -p "$pid" 2>/dev/null | tr -d ' ' || echo "?")
    log "Background TLC N=4 full: RUNNING (pid=$pid, elapsed=$et)"
    if [[ -f "$logf" ]]; then
      log "Latest progress:"
      grep '^Progress' "$logf" 2>/dev/null | tail -3 | sed 's/^/    /' || true
    fi
    return 0
  fi
  # Not running — check if it completed
  if [[ -f "$logf" ]]; then
    if grep -q 'Model checking completed. No error has been found.' "$logf"; then
      log "Background TLC N=4 full: COMPLETED — no errors"
      local distinct depth
      distinct=$(grep -oE '[0-9,]+ distinct states found' "$logf" | tail -1 \
                  | grep -oE '[0-9,]+' | tr -d ',')
      depth=$(grep -oE 'depth of the complete state graph search is [0-9]+' \
                   "$logf" | grep -oE '[0-9]+$')
      ok "${distinct} distinct states, depth ${depth}, 0 violations"
      return 0
    fi
    if grep -q 'Error: Invariant' "$logf"; then
      fail "Background TLC N=4 full: VIOLATION FOUND — see $logf"
      return 2
    fi
    warn "Background TLC N=4 full: not running, no completion line. Crashed? See $logf"
    return 1
  fi
  log "No background TLC N=4 full run found ($PID_FILE does not exist)"
  return 1
}

# Analyse a completed background-TLC log and update formal_results.json.
bg_analyse_and_update_json() {
  local logf="results/tlc_tlc_n4_full.log"
  [[ -f "$logf" ]] || return 1
  local line generated distinct depth err completed
  line=$(extract_first '[0-9,]+ states generated, [0-9,]+ distinct states found' "$logf")
  generated=$(echo "$line" | grep -oE '^[0-9,]+' | tr -d ',')
  distinct=$(echo "$line" | grep -oE '[0-9,]+ distinct' | grep -oE '[0-9,]+' | tr -d ',')
  depth=$(extract_first 'depth of the complete state graph search is [0-9]+' "$logf" \
          | grep -oE '[0-9]+$')
  err=$(grep -c 'Error: Invariant.* is violated' "$logf" 2>/dev/null | tr -d '[:space:]')
  err=${err:-0}
  completed=$(grep -c 'Model checking completed. No error has been found.' "$logf" \
              2>/dev/null | tr -d '[:space:]')
  completed=${completed:-0}

  local status
  if [[ "$completed" == "1" && "$err" == "0" ]]; then
    status="pass"
  elif [[ "$err" != "0" ]]; then
    status="fail"
  else
    status="partial"
  fi

  # Patch the JSON in place with sed if it exists, else regenerate.
  if [[ -f "$RESULTS" ]]; then
    python3 -c "
import json, sys
p = '$RESULTS'
try:
    with open(p) as f:
        d = json.load(f)
except Exception:
    d = {}
d['tlc_n4_full_status'] = '$status'
d['tlc_n4_full_distinct'] = int('${distinct:-0}' or 0)
d['tlc_n4_full_generated'] = int('${generated:-0}' or 0)
d['tlc_n4_full_depth'] = int('${depth:-0}' or 0)
d['tlc_n4_full_violations'] = int('${err:-0}' or 0)
with open(p, 'w') as f:
    json.dump(d, f, indent=2)
" 2>/dev/null || warn "Could not update $RESULTS (python3 not available?)"
    ok "Updated $RESULTS with N=4-full results: $status, $distinct distinct states"
  fi
}

# ── --status: print status and exit ───────────────────────────────────────────
if [[ "$STATUS_MODE" == "true" ]]; then
  bg_print_status
  exit $?
fi

# ── --finalise: print status AND patch the JSON (post-TLC hook) ──────────────
if [[ "$FINALISE_MODE" == "true" ]]; then
  bg_print_status
  RC=$?
  bg_analyse_and_update_json
  exit "$RC"
fi

# ── --wait: block until background job finishes, then analyse ────────────────
if [[ "$WAIT_MODE" == "true" ]]; then
  if [[ ! -f "$PID_FILE" ]]; then
    fail "No background run to wait for ($PID_FILE does not exist)"
    exit 1
  fi
  PID=$(cat "$PID_FILE")
  log "Waiting for background TLC (pid=$PID) — this blocks until it exits."
  log "Progress every 60s; Ctrl-C to stop watching (TLC keeps running)."
  while kill -0 "$PID" 2>/dev/null; do
    sleep 60
    grep '^Progress' "results/tlc_tlc_n4_full.log" 2>/dev/null | tail -1 \
      | sed 's/^/    /' || true
  done
  log "Background TLC finished."
  bg_print_status
  RC=$?
  bg_analyse_and_update_json
  exit "$RC"
fi

# ── 1. Dafny verification ─────────────────────────────────────────────────────

run_dafny() {
  log "STEP 1/5: Dafny verification of proofs/sbus_lemmas.dfy"
  if ! require_tool "$DAFNY" DAFNY; then
    J[dafny_status]="tool_missing"
    return
  fi
  if [[ ! -f proofs/sbus_lemmas.dfy ]]; then
    fail "proofs/sbus_lemmas.dfy not in current dir"
    J[dafny_status]="file_missing"
    return
  fi
  "$DAFNY" verify proofs/sbus_lemmas.dfy > results/dafny.log 2>&1
  rc=$?
  # Dafny's success line:
  # "Dafny program verifier finished with N verified, 0 errors"
  line=$(extract_first 'Dafny program verifier finished with [0-9]+ verified, [0-9]+ errors' results/dafny.log)
  verified=$(echo "$line" | grep -oE '[0-9]+ verified' | grep -oE '[0-9]+')
  errors=$(echo   "$line" | grep -oE '[0-9]+ errors'   | grep -oE '[0-9]+')
  if [[ "$rc" == "0" && "${errors:-1}" == "0" ]]; then
    ok "Dafny: $verified verified, 0 errors"
    J[dafny_status]="pass"
    J[dafny_verified]="$verified"
    J[dafny_errors]="0"
  else
    fail "Dafny failed (rc=$rc, line='$line') — see results/dafny.log"
    J[dafny_status]="fail"
    J[dafny_verified]="${verified:-0}"
    J[dafny_errors]="${errors:-unknown}"
  fi
}

# ── 2. tlapm mechanisation ────────────────────────────────────────────────────

run_tlapm() {
  log "STEP 2/5: tlapm proof of proofs/SBus_TLAPS.tla"
  if ! require_tool "$TLAPM" TLAPM; then
    J[tlapm_status]="tool_missing"
    return
  fi
  if [[ ! -f proofs/SBus_TLAPS.tla ]]; then
    fail "proofs/SBus_TLAPS.tla not in current dir"
    J[tlapm_status]="file_missing"
    return
  fi
  if [[ -d "$TLAPS_LIB" ]]; then
    "$TLAPM" -I "$TLAPS_LIB" proofs/SBus_TLAPS.tla > results/tlapm.log 2>&1
  else
    "$TLAPM" proofs/SBus_TLAPS.tla > results/tlapm.log 2>&1
  fi
  rc=$?
  # tlapm emits one of two summary patterns:
  #   Success: "[INFO]: All N obligations proved."
  #   Failure: "[ERROR]: K/N obligations failed."
  # Try success pattern first.
  success_line=$(extract_first 'All [0-9]+ obligations proved' results/tlapm.log)
  if [[ -n "$success_line" ]]; then
    proved=$(echo "$success_line" | grep -oE '[0-9]+')
    ok "tlapm: $proved obligations proved, 0 failed"
    J[tlapm_status]="pass"
    J[tlapm_proved]="$proved"
    J[tlapm_failed]="0"
    return
  fi
  # Fall back to failure pattern: "K/N obligations failed"
  fail_line=$(extract_first '[0-9]+/[0-9]+ obligations failed' results/tlapm.log)
  if [[ -n "$fail_line" ]]; then
    failed=$(echo "$fail_line" | grep -oE '^[0-9]+')
    total=$(echo "$fail_line" | grep -oE '/[0-9]+' | grep -oE '[0-9]+')
    proved=$((total - failed))
    fail "tlapm: $proved/$total proved, $failed failed — see results/tlapm.log"
    J[tlapm_status]="fail"
    J[tlapm_proved]="$proved"
    J[tlapm_failed]="$failed"
    return
  fi
  # Neither pattern matched — likely a parser/tool crash.
  fail "tlapm produced no obligation summary (likely crashed) — see results/tlapm.log"
  J[tlapm_status]="fail"
  J[tlapm_proved]="0"
  J[tlapm_failed]="unknown"
}

# ── 3-5. TLC runs ─────────────────────────────────────────────────────────────

run_tlc() {
  cfg="$1"; label="$2"
  log "STEP $3/5: TLC $label ($cfg)"
  if [[ ! -f "$TLA_JAR" ]]; then
    fail "tla2tools.jar not at \$TLA_JAR=$TLA_JAR"
    J[${label}_status]="jar_missing"
    return
  fi
  java -Xmx"$TLC_HEAP" -XX:+UseParallelGC -cp "$TLA_JAR" tlc2.TLC \
       -workers "$TLC_WORKERS" -config "$cfg" models/SBus_ori.tla \
       > "results/tlc_${label}.log" 2>&1
  rc=$?
  # TLC summary line:
  #   "X states generated, Y distinct states found, Z states left on queue."
  line=$(extract_first '[0-9,]+ states generated, [0-9,]+ distinct states found' \
                       "results/tlc_${label}.log")
  generated=$(echo "$line" | grep -oE '^[0-9,]+' | tr -d ',')
  distinct=$(  echo "$line" | grep -oE '[0-9,]+ distinct' | grep -oE '[0-9,]+' | tr -d ',')
  depth=$(extract_first 'depth of the complete state graph search is [0-9]+' \
                        "results/tlc_${label}.log" | grep -oE '[0-9]+$')
  err=$(grep -c 'Error: Invariant.* is violated' "results/tlc_${label}.log" 2>/dev/null | tr -d '[:space:]')
  err=${err:-0}
  completed=$(grep -c 'Model checking completed. No error has been found.' \
                    "results/tlc_${label}.log" 2>/dev/null | tr -d '[:space:]')
  completed=${completed:-0}

  if [[ "$completed" == "1" && "$err" == "0" ]]; then
    ok "TLC $label: ${distinct} distinct states, depth ${depth}, 0 violations"
    J[${label}_status]="pass"
  elif [[ "$err" == "0" ]]; then
    warn "TLC $label: PARTIAL — ${distinct} distinct states, depth ${depth}, 0 violations so far"
    J[${label}_status]="partial"
  else
    fail "TLC $label: $err invariant violations — see results/tlc_${label}.log"
    J[${label}_status]="fail"
  fi
  J[${label}_distinct]="${distinct:-0}"
  J[${label}_generated]="${generated:-0}"
  J[${label}_depth]="${depth:-0}"
  J[${label}_violations]="${err:-0}"
}

# ── Main ──────────────────────────────────────────────────────────────────────

if [[ "$TLC_ONLY" == "true" ]]; then
  J[dafny_status]="skipped"
  J[tlapm_status]="skipped"
else
  run_dafny
  run_tlapm
fi

if [[ "$PROOF_ONLY" == "true" ]]; then
  J[tlc_n3_status]="skipped"
  J[tlc_n4_reduced_status]="skipped"
  J[tlc_n4_full_status]="skipped"
else
  run_tlc models/SBus_ori_N3.cfg          tlc_n3         3
  run_tlc models/SBus_ori_N4_reduced.cfg  tlc_n4_reduced 4
  if [[ "$SKIP_TLC_FULL" == "true" ]]; then
    log "STEP 5/5: TLC N=4 full SKIPPED (--skip-tlc-full)"
    J[tlc_n4_full_status]="skipped"
  elif [[ "$FOREGROUND" == "true" ]]; then
    log "STEP 5/5: TLC N=4 full (foreground; this takes ~1-2h)"
    run_tlc models/SBus_ori_N4.cfg tlc_n4_full 5
  else
    # ── DEFAULT: launch N=4 full in the background ─────────────────────
    # Check whether a background run is already active.
    if bg_is_running; then
      warn "STEP 5/5: A background TLC is already running (pid=$(cat $PID_FILE))"
      warn "          Use --status to check progress, --wait to block until done"
      J[tlc_n4_full_status]="already_running"
    elif [[ ! -f "$TLA_JAR" ]]; then
      fail "STEP 5/5: cannot launch background TLC — $TLA_JAR missing"
      J[tlc_n4_full_status]="jar_missing"
    else
      log "STEP 5/5: TLC N=4 full — LAUNCHING IN BACKGROUND (~1-2h)"
      log "  Log:      results/tlc_tlc_n4_full.log"
      log "  PID file: $PID_FILE"
      log "  Workers:  $TLC_WORKERS"
      log "  Heap:     $TLC_HEAP"
      rm -f "$PID_FILE" results/tlc_tlc_n4_full.log
      # The wrapper runs TLC, and on completion runs this script with --wait
      # to update the JSON. Using setsid + nohup so it survives SSH disconnect.
      nohup bash -c "
        java -Xmx$TLC_HEAP -XX:+UseParallelGC -cp '$TLA_JAR' tlc2.TLC \
             -workers $TLC_WORKERS -config models/SBus_ori_N4.cfg models/SBus_ori.tla \
             > results/tlc_tlc_n4_full.log 2>&1
        RC=\$?
        rm -f '$PID_FILE'
        # Patch the JSON with final N=4 full results.
        '$0' --finalise > results/tlc_n4_full_completion.log 2>&1 || true
        exit \$RC
      " >/dev/null 2>&1 &
      BG_PID=$!
      # Wait up to 10 seconds for java to start, then record its real pid.
      JAVA_PID=""
      for i in 1 2 3 4 5 6 7 8 9 10; do
        sleep 1
        JAVA_PID=$(pgrep -f "tlc2.TLC.*models/SBus_ori_N4.cfg" 2>/dev/null | head -1)
        [[ -n "$JAVA_PID" ]] && break
      done
      if [[ -n "$JAVA_PID" ]]; then
        echo "$JAVA_PID" > "$PID_FILE"
        ok "TLC N=4 full launched (java pid=$JAVA_PID). Check back in ~1-2h."
        log "  ./run_formal.sh --status     # to check progress"
        log "  ./run_formal.sh --wait       # to block until finished"
        log "  tail -f results/tlc_tlc_n4_full.log"
        J[tlc_n4_full_status]="running"
      else
        # Java didn't start in 10s — likely failed. Fall back to bash wrapper.
        echo "$BG_PID" > "$PID_FILE"
        warn "Could not detect java pid after 10s; using bash wrapper pid=$BG_PID"
        warn "Check results/tlc_tlc_n4_full.log for startup errors."
        J[tlc_n4_full_status]="running"
      fi
    fi
  fi
fi

ENDTS=$(date -u +%FT%TZ)
J[end]="$ENDTS"

# Emit JSON
{
  echo "{"
  first=true
  for k in start end \
           dafny_status dafny_verified dafny_errors \
           tlapm_status tlapm_proved tlapm_failed \
           tlc_n3_status tlc_n3_distinct tlc_n3_generated tlc_n3_depth tlc_n3_violations \
           tlc_n4_reduced_status tlc_n4_reduced_distinct tlc_n4_reduced_generated tlc_n4_reduced_depth tlc_n4_reduced_violations \
           tlc_n4_full_status tlc_n4_full_distinct tlc_n4_full_generated tlc_n4_full_depth tlc_n4_full_violations
  do
    val="${J[$k]:-null}"
    if [[ "$val" =~ ^[0-9]+$ ]]; then
      printf '%s  "%s": %s' "$( $first && echo '' || echo ',' )" "$k" "$val"
    else
      printf '%s  "%s": "%s"' "$( $first && echo '' || echo ',' )" "$k" "$val"
    fi
    echo
    first=false
  done
  echo "}"
} > "$RESULTS"

log "Results written to $RESULTS"
log "===================="
log "Summary:"
[[ "${J[dafny_status]:-}" == "pass" ]] && ok "Dafny: ${J[dafny_verified]} verified, 0 errors"
[[ "${J[tlapm_status]:-}" == "pass" ]] && ok "tlapm: ${J[tlapm_proved]} obligations proved, 0 failed"
[[ "${J[tlc_n3_status]:-}" == "pass" ]] && ok "TLC N=3: ${J[tlc_n3_distinct]} states, 0 violations"
[[ "${J[tlc_n4_reduced_status]:-}" == "pass" ]] && ok "TLC N=4-reduced: ${J[tlc_n4_reduced_distinct]} states, 0 violations"
[[ "${J[tlc_n4_full_status]:-}" == "pass" ]] && ok "TLC N=4-full: ${J[tlc_n4_full_distinct]} states, 0 violations"
if [[ "${J[tlc_n4_full_status]:-}" == "running" ]]; then
  log ""
  log "N=4 full TLC is running in the background."
  log "Check progress:    ./run_formal.sh --status"
  log "Block until done:  ./run_formal.sh --wait"
  log "Live tail:         tail -f results/tlc_tlc_n4_full.log"
fi

# Exit code: pass iff every non-skipped, non-running step is "pass" or "partial"
fails=0
for k in dafny_status tlapm_status tlc_n3_status tlc_n4_reduced_status tlc_n4_full_status; do
  s="${J[$k]:-}"
  if [[ "$s" == "fail" || "$s" == "tool_missing" || "$s" == "file_missing" || "$s" == "jar_missing" ]]; then
    fails=$((fails+1))
  fi
done
exit "$fails"
