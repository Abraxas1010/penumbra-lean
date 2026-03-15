#!/usr/bin/env bash
set -euo pipefail

echo "╔══════════════════════════════════════════════════════════╗"
echo "║     Penumbra — Independent Verification Suite           ║"
echo "╚══════════════════════════════════════════════════════════╝"
echo ""

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
LEAN_DIR="$REPO_ROOT/lean"

echo "Step 1/4: Building all modules..."
(cd "$LEAN_DIR" && lake build)
echo "  ✓ Build succeeded"
echo ""

echo "Step 2/4: Checking for sorry/admit..."
count=$(grep -rn "sorry\|admit" "$LEAN_DIR/HeytingLean/" --include="*.lean" \
  | grep -v "^\s*--\|/--\|import\|guard_no_sorry\|NoSorry\|sorry_free\|sorry_count\|sorryCount\|has_sorry\|hasSorry\|\.sorry\|noSorry\|anti_sorry\|\"sorry\"\|sorry-\|sorry_" \
  | wc -l || true)
if [ "$count" -gt 0 ]; then
  echo "  ✗ FAIL: $count sorry/admit found"
  grep -rn "sorry\|admit" "$LEAN_DIR/HeytingLean/" --include="*.lean" \
    | grep -v "^\s*--\|/--\|import\|guard_no_sorry\|NoSorry\|sorry_free"
  exit 1
fi
echo "  ✓ Zero sorry/admit"
echo ""

echo "Step 3/4: Counting declarations..."
file_count=$(find "$LEAN_DIR/HeytingLean" -name "*.lean" | wc -l)
thm_count=$(grep -rc "^theorem\|^lemma" "$LEAN_DIR/HeytingLean/" --include="*.lean" \
  | awk -F: '{s+=$2} END {print s}')
decl_count=$(grep -rc "^theorem\|^lemma\|^def \|^noncomputable def \|^instance \|^class \|^structure " \
  "$LEAN_DIR/HeytingLean/" --include="*.lean" \
  | awk -F: '{s+=$2} END {print s}')
echo "  Files:            $file_count"
echo "  Theorems/lemmas:  $thm_count"
echo "  Total declarations: $decl_count"
echo ""

echo "Step 4/4: Verifying import closure..."
missing=0
while IFS= read -r line; do
  mod=$(echo "$line" | sed 's/import //' | tr '.' '/')
  if [ ! -f "$LEAN_DIR/${mod}.lean" ]; then
    echo "  MISSING: $mod"
    missing=$((missing + 1))
  fi
done < <(grep -rh "^import HeytingLean" "$LEAN_DIR/" | sort -u)
if [ "$missing" -gt 0 ]; then
  echo "  ✗ FAIL: $missing missing imports"
  exit 1
fi
echo "  ✓ All imports resolve"
echo ""

echo "╔══════════════════════════════════════════════════════════╗"
echo "║                 VERIFICATION PASSED                     ║"
echo "║  $file_count files, $decl_count declarations, 0 sorry              ║"
echo "╚══════════════════════════════════════════════════════════╝"
