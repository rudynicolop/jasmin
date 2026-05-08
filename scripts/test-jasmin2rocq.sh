#!/bin/bash
# Test script for jasmin2rocq printer
# Runs jasmin2rocq on all example programs in compiler/examples,
# wraps each output in a .v file, and type-checks with coqc.
# Tests three modes: default, --split, and --imports (self-contained).

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
JASMIN2ROCQ="$ROOT_DIR/compiler/jasmin2rocq"
EXAMPLES_DIR="$ROOT_DIR/compiler/examples"
PROOFS_DIR="$ROOT_DIR/proofs"
OUTDIR=$(mktemp -d)

trap "rm -rf $OUTDIR" EXIT

PASS=0
FAIL=0

COQC_FLAGS=(
  -R "$PROOFS_DIR/3rdparty" Jasmin
  -R "$PROOFS_DIR/arch" Jasmin
  -R "$PROOFS_DIR/compiler" Jasmin
  -R "$PROOFS_DIR/lang" Jasmin
  -R "$PROOFS_DIR/ssrmisc" Jasmin
  -R "$PROOFS_DIR/itrees" Jasmin
  -w -all
)

PREAMBLE='From mathcomp Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ZArith.
Require Import expr ident var type global warray_ pseudo_operator sopn arch_extra.
Require Import x86_decl x86_instr_decl x86_extra.
Import Utf8.

Axiom mkvar : atype -> string -> var_i.
Axiom mkfun : string -> funname.
Axiom atoI : arch_toIdent.
#[local] Existing Instance atoI.
#[local] Coercion gv : gvar >-> var_i.
'

# Collect all .jazz files under compiler/examples
FILES=()
while IFS= read -r -d '' f; do
  FILES+=("$f")
done < <(find "$EXAMPLES_DIR" -name '*.jazz' -print0 | sort -z)

# run_test MODE EXTRA_FLAGS...
# MODE is a label for the test output; EXTRA_FLAGS are passed to jasmin2rocq.
# When --imports is among EXTRA_FLAGS, the output is self-contained (no preamble needed).
run_test() {
  local mode="$1"; shift
  local extra_flags=("$@")
  local needs_preamble=true
  for f in "${extra_flags[@]}"; do
    [ "$f" = "--imports" ] && needs_preamble=false
  done

  for jazz_file in "${FILES[@]}"; do
    local rel_path="${jazz_file#$EXAMPLES_DIR/}"
    local test_name=$(echo "$rel_path" | sed 's|[/.-]|_|g; s|_jazz$||')
    local v_file="$OUTDIR/test_${mode}_${test_name}.v"

    # Run jasmin2rocq
    local rocq_output
    rocq_output=$("$JASMIN2ROCQ" "${extra_flags[@]}" "$jazz_file" 2>/dev/null) || {
      echo "FAIL [$mode] $rel_path (jasmin2rocq failed)"
      FAIL=$((FAIL + 1))
      continue
    }

    # Generate .v file
    if $needs_preamble; then
      printf '%s\n%s\n' "$PREAMBLE" "$rocq_output" > "$v_file"
    else
      printf '%s\n' "$rocq_output" > "$v_file"
    fi

    # Type-check
    if coqc "${COQC_FLAGS[@]}" "$v_file" 2>/dev/null; then
      echo "PASS [$mode] $rel_path"
      PASS=$((PASS + 1))
    else
      echo "FAIL [$mode] $rel_path"
      FAIL=$((FAIL + 1))
    fi
  done
}

TOTAL=$(( ${#FILES[@]} * 3 ))
echo "Running jasmin2rocq tests on ${#FILES[@]} files x 3 modes..."
echo ""

run_test "default"
run_test "split" --split
run_test "imports" --imports

echo ""
echo "Results: $PASS passed, $FAIL failed (total: $TOTAL)"

if [ "$FAIL" -gt 0 ]; then
  exit 1
fi
