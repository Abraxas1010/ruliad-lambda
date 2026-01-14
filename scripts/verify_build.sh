#!/usr/bin/env bash
# Ruliad Lambda - Build Verification Script
# Verifies the formal proofs compile correctly

set -e

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║     RULIAD LAMBDA - BUILD VERIFICATION                    ║"
echo "║     Machine-verified proofs for λ-calculus ruliology      ║"
echo "╚═══════════════════════════════════════════════════════════╝"
echo

cd "$(dirname "$0")/.."

# Check for sorry/admit
echo "▶ Checking for sorry/admit..."
if grep -rn "sorry\|admit" HeytingLean/ --include="*.lean" 2>/dev/null; then
    echo "✗ Found sorry/admit in codebase!"
    exit 1
fi
echo "✓ No sorry/admit found"
echo

# Build library
echo "▶ Building library (lake build --wfail)..."
lake build --wfail
echo "✓ Library build successful"
echo

# Build executable
echo "▶ Building lambda_multiway_demo executable..."
lake build lambda_multiway_demo
echo "✓ Executable build successful"
echo

# Run demo
echo "▶ Running multiway demo..."
lake exe lambda_multiway_demo
echo "✓ Demo execution successful"
echo

echo "╔═══════════════════════════════════════════════════════════╗"
echo "║     ALL VERIFICATIONS PASSED                              ║"
echo "║                                                           ║"
echo "║     Key theorems verified:                                ║"
echo "║     • Church-Rosser (confluence)                          ║"
echo "║     • λ ↔ SK simulation                                   ║"
echo "║     • β-reduction termination properties                  ║"
echo "╚═══════════════════════════════════════════════════════════╝"
