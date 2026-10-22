#!/bin/bash
# Gate for the Fivecircles Lean formalisation. Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="Fivecircles"
LIB="Fivecircles"
REQUIRED="Fivecircles.fivecircles Fivecircles.core Fivecircles.cd_of_concyclic Fivecircles.col3_of_collinear Fivecircles.concyclic_of Fivecircles.collinear_of Fivecircles.l14_fivecircles Fivecircles.l14b_collinear4 Fivecircles.l14b_concyclic_of_normSq Fivecircles.l14b_not_collinear Fivecircles.l14w_fivecircles Fivecircles.Classical.cov_cospherical_transport Fivecircles.Classical.cov_collinear_transport Fivecircles.Classical.cov_D2_part Fivecircles.Classical.gap_sphere_line Fivecircles.Classical.gap_idx_V Fivecircles.Classical.gap_idx_T Fivecircles.Classical.gap_idx_VT Fivecircles.Classical.gap_idx_ne Fivecircles.Classical.gap_idx_VQ Fivecircles.Classical.gap_idx_TQ Fivecircles.Classical.gap_D2_distinct Fivecircles.Classical.cov_D2_injQ Fivecircles.Classical.gap_core_distinct Fivecircles.Classical.gap_cd_degen Fivecircles.Classical.gap_core Fivecircles.Classical.gap_cd_perms Fivecircles.Classical.gap_cd_all_00 Fivecircles.Classical.gap_cd_all_01 Fivecircles.Classical.gap_cd_all_02 Fivecircles.Classical.gap_cd_all_03 Fivecircles.Classical.gap_cd_all_04 Fivecircles.Classical.gap_cd_all_10 Fivecircles.Classical.gap_cd_all_11 Fivecircles.Classical.gap_cd_all_12 Fivecircles.Classical.gap_cd_all_13 Fivecircles.Classical.gap_cd_all_14 Fivecircles.Classical.gap_cd_all_20 Fivecircles.Classical.gap_cd_all_21 Fivecircles.Classical.gap_cd_all_22 Fivecircles.Classical.gap_cd_all_23 Fivecircles.Classical.gap_cd_all_24 Fivecircles.Classical.gap_cd_all_30 Fivecircles.Classical.gap_cd_all_31 Fivecircles.Classical.gap_cd_all_32 Fivecircles.Classical.gap_cd_all_33 Fivecircles.Classical.gap_cd_all_34 Fivecircles.Classical.gap_cd_all_40 Fivecircles.Classical.gap_cd_all_41 Fivecircles.Classical.gap_cd_all_42 Fivecircles.Classical.gap_cd_all_43 Fivecircles.Classical.gap_cd_all_44 Fivecircles.Classical.gap_cd_all Fivecircles.Classical.gap_fivecircles Fivecircles.Classical.cov_D2 Fivecircles.Classical.cov_D2_exact Fivecircles.Classical.gap_line_ne_bot Fivecircles.Classical.gap_lines_meet Fivecircles.Classical.gap_idx_obl Fivecircles.Classical.cov_D2_obligation Fivecircles.Classical.cov_D2_obligation_exact"
SOURCES="Fivecircles/*.lean Fivecircles.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
