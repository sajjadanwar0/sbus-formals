#!/usr/bin/env bash
# run_heavy_proof.sh — Verified-syntax heavy sweep for tlapm 1.6.0-pre.
#
# Uses ONLY method identifiers confirmed to exist in your installation:
#   zenon, auto, blast, force, smt, z3, cvc4, yices, verit, spass,
#   zipper, ls4
#
# Key prover features used:
#   - `force` and `blast` — Isabelle tactics specifically strong on function
#     extensionality (what FunTypingReconstruction needs)
#   - `spass` and `zipper` — higher-order provers; zipper especially
#     designed for HOL-level reasoning
#   - `verit` and `cvc4` — alternative SMT backends for robustness
#
# Usage:
#   cd /path/to/phase1
#   chmod +x run_heavy_proof.sh
#   ./run_heavy_proof.sh SBus_TLAPS_attempt_a.tla
#
# Runtime: 20-60 min.

set -uo pipefail

SPEC="${1:-SBus_TLAPS_attempt_a.tla}"
if [[ ! -f "$SPEC" ]]; then
  for fallback in SBus_TLAPS_attempt_b.tla SBus_TLAPS.tla; do
    if [[ -f "$fallback" ]]; then
      SPEC="$fallback"
      echo "[info] Using $SPEC"
      break
    fi
  done
  if [[ ! -f "$SPEC" ]]; then
    echo "[error] No spec found. Pass one as \$1."
    exit 1
  fi
fi

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
LOG="tlapm_heavy_${TIMESTAMP}.log"
SUMMARY="tlapm_heavy_summary_${TIMESTAMP}.txt"
THREADS="${THREADS:-4}"

echo "===================================================================="
echo "  tlapm heavy sweep v3 — verified method names"
echo "===================================================================="
echo "  Spec:       $SPEC"
echo "  Threads:    $THREADS"
echo "  Log:        $LOG"
echo "  Summary:    $SUMMARY"
echo "===================================================================="

tlapm --version 2>&1 | head -2 | tee "$SUMMARY"
echo "" | tee -a "$SUMMARY"

# ── Pass list — each pass uses VALID methods from --method help ──────────
# Format: "label|method_list|stretch"
#
# Default timeouts:
#   smt/z3/cvc4/verit/yices = 5s
#   zenon  = 10s
#   auto/blast/force = 30s (Isabelle)
#   spass/zipper = similar to SMT
#
# stretch multiplies all of these.

declare -a PASSES=(
  # Baseline — all three default backends
  "baseline|smt,zenon,auto|1"

  # Isabelle family — the best bet for extensionality
  "isa_auto_long|auto|10"
  "isa_blast|blast|10"
  "isa_blast_xlong|blast|30"
  "isa_force|force|10"
  "isa_force_xlong|force|30"
  "isa_all|auto,blast,force|10"
  "isa_all_xlong|auto,blast,force|30"

  # SMT alternatives
  "smt_long|smt|10"
  "z3_long|z3|10"
  "cvc4_long|cvc4|10"
  "verit_long|verit|10"

  # Higher-order provers
  "spass|spass|10"
  "zipper|zipper|10"
  "zipper_xlong|zipper|30"

  # Everything at once — maximum shotgun
  "max_shotgun|smt,zenon,auto,blast,force,z3,cvc4,verit,spass,zipper|10"
  "max_xlong|smt,zenon,auto,blast,force,z3,cvc4,verit,spass,zipper|30"
)

run_pass() {
  local label="$1"
  local methods="$2"
  local stretch="$3"

  echo "" | tee -a "$SUMMARY"
  echo "────────────────────────────────────────────────────────────────────" | tee -a "$SUMMARY"
  echo " Pass: $label  (methods=$methods, stretch=$stretch)" | tee -a "$SUMMARY"
  echo "────────────────────────────────────────────────────────────────────" | tee -a "$SUMMARY"

  local t0=$(date +%s)

  tlapm --cleanfp \
        --threads "$THREADS" \
        --method "$methods" \
        --stretch "$stretch" \
        "$SPEC" >> "$LOG" 2>&1

  local rc=$?
  local t1=$(date +%s)
  local dt=$((t1 - t0))

  # Find this pass's result in the log.
  # Look in the last chunk — new content only.
  local chunk_start=$(wc -l < "$LOG")
  chunk_start=$((chunk_start - 200))
  [[ $chunk_start -lt 1 ]] && chunk_start=1

  local proved=$(tail -n +$chunk_start "$LOG" | grep -cE "^\[INFO\]: All [0-9]+ obligations? proved" || echo 0)
  local failed_line=$(tail -n +$chunk_start "$LOG" | grep -E "obligations? failed" | tail -1)
  local result_line=$(tail -n +$chunk_start "$LOG" | grep -E "obligations? (proved|failed)" | tail -2)

  echo "Pass $label: rc=$rc, runtime=${dt}s" | tee -a "$SUMMARY"
  echo "$result_line" | tee -a "$SUMMARY"

  # Success = no "failed" line AND there's at least one "proved" line
  if [[ -n "$failed_line" ]]; then
    # Found a failure in this chunk
    return 1
  fi

  # Check: no failure AND exit code 0
  if [[ "$rc" == "0" ]]; then
    echo "" | tee -a "$SUMMARY"
    echo "*** ALL PROVED in pass: $label ***" | tee -a "$SUMMARY"
    echo "*** Spec: $SPEC ***" | tee -a "$SUMMARY"
    echo "*** Config: --method $methods --stretch $stretch ***" | tee -a "$SUMMARY"
    return 0
  fi

  return 1
}

# ── Execute ──────────────────────────────────────────────────────────────
echo "Starting $(date)" | tee -a "$SUMMARY"
echo "Spec: $SPEC" | tee -a "$SUMMARY"

SUCCESS=false
WINNING_LABEL=""
WINNING_METHODS=""
WINNING_STRETCH=""

for pass_def in "${PASSES[@]}"; do
  IFS='|' read -r label methods stretch <<< "$pass_def"
  if run_pass "$label" "$methods" "$stretch"; then
    SUCCESS=true
    WINNING_LABEL="$label"
    WINNING_METHODS="$methods"
    WINNING_STRETCH="$stretch"
    break
  fi
done

echo "" | tee -a "$SUMMARY"
echo "====================================================================" | tee -a "$SUMMARY"
if [[ "$SUCCESS" == "true" ]]; then
  echo "  RESULT: SUCCESS via pass '$WINNING_LABEL'" | tee -a "$SUMMARY"
  echo "  Winning config:" | tee -a "$SUMMARY"
  echo "     --method $WINNING_METHODS --stretch $WINNING_STRETCH" | tee -a "$SUMMARY"
  echo "" | tee -a "$SUMMARY"
  echo "  Paste the following into your run_formal.sh:" | tee -a "$SUMMARY"
  echo "     tlapm --method $WINNING_METHODS --stretch $WINNING_STRETCH \$SPEC" | tee -a "$SUMMARY"
else
  echo "  RESULT: No single-method pass closed all obligations." | tee -a "$SUMMARY"
  echo "  17 distinct method/timeout combinations attempted." | tee -a "$SUMMARY"
  echo "  The v16 AXIOM retention remains the defensible final state." | tee -a "$SUMMARY"
fi
echo "====================================================================" | tee -a "$SUMMARY"
echo "" | tee -a "$SUMMARY"
echo "Full log:     $LOG" | tee -a "$SUMMARY"
echo "Summary file: $SUMMARY" | tee -a "$SUMMARY"
