#!/usr/bin/env bash

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

echo "  tlapm heavy sweep v3 — verified method names"
echo "  Spec:       $SPEC"
echo "  Threads:    $THREADS"
echo "  Log:        $LOG"
echo "  Summary:    $SUMMARY"

tlapm --version 2>&1 | head -2 | tee "$SUMMARY"
echo "" | tee -a "$SUMMARY"


declare -a PASSES=(
  "baseline|smt,zenon,auto|1"

  "isa_auto_long|auto|10"
  "isa_blast|blast|10"
  "isa_blast_xlong|blast|30"
  "isa_force|force|10"
  "isa_force_xlong|force|30"
  "isa_all|auto,blast,force|10"
  "isa_all_xlong|auto,blast,force|30"

  "smt_long|smt|10"
  "z3_long|z3|10"
  "cvc4_long|cvc4|10"
  "verit_long|verit|10"

  "spass|spass|10"
  "zipper|zipper|10"
  "zipper_xlong|zipper|30"

  "max_shotgun|smt,zenon,auto,blast,force,z3,cvc4,verit,spass,zipper|10"
  "max_xlong|smt,zenon,auto,blast,force,z3,cvc4,verit,spass,zipper|30"
)

run_pass() {
  local label="$1"
  local methods="$2"
  local stretch="$3"

  echo "" | tee -a "$SUMMARY"
  echo "--------------------------------------------------------------------" | tee -a "$SUMMARY"
  echo " Pass: $label  (methods=$methods, stretch=$stretch)" | tee -a "$SUMMARY"
  echo "--------------------------------------------------------------------" | tee -a "$SUMMARY"

  local t0=$(date +%s)

  tlapm --cleanfp \
        --threads "$THREADS" \
        --method "$methods" \
        --stretch "$stretch" \
        "$SPEC" >> "$LOG" 2>&1

  local rc=$?
  local t1=$(date +%s)
  local dt=$((t1 - t0))

  local chunk_start=$(wc -l < "$LOG")
  chunk_start=$((chunk_start - 200))
  [[ $chunk_start -lt 1 ]] && chunk_start=1

  local proved=$(tail -n +$chunk_start "$LOG" | grep -cE "^\[INFO\]: All [0-9]+ obligations? proved" || echo 0)
  local failed_line=$(tail -n +$chunk_start "$LOG" | grep -E "obligations? failed" | tail -1)
  local result_line=$(tail -n +$chunk_start "$LOG" | grep -E "obligations? (proved|failed)" | tail -2)

  echo "Pass $label: rc=$rc, runtime=${dt}s" | tee -a "$SUMMARY"
  echo "$result_line" | tee -a "$SUMMARY"

  if [[ -n "$failed_line" ]]; then
    return 1
  fi

  if [[ "$rc" == "0" ]]; then
    echo "" | tee -a "$SUMMARY"
    echo "*** ALL PROVED in pass: $label ***" | tee -a "$SUMMARY"
    echo "*** Spec: $SPEC ***" | tee -a "$SUMMARY"
    echo "*** Config: --method $methods --stretch $stretch ***" | tee -a "$SUMMARY"
    return 0
  fi

  return 1
}

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