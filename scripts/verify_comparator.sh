#!/bin/bash
# Comparator verification script for ArtificialTheorems
#
# This script runs the comparator tool to verify that implementations
# prove exactly the theorems specified in the challenge (spec) modules.
#
# PREREQUISITES:
#   - landrun: https://github.com/Zouuup/landrun
#   - lean4export: https://github.com/leanprover/lean4export (matching Lean version)
#   - comparator: https://github.com/leanprover/comparator
#
# All three tools must be built and available in PATH, or you can set
# COMPARATOR_BIN environment variable to point to the comparator binary.
#
# IMPORTANT: For secure verification, ensure solution modules have NOT been
# previously compiled in your environment. Run this script from a clean state
# (fresh clone or after `lake clean`).
#
# Usage:
#   ./scripts/verify_comparator.sh [config_file]
#
# If no config_file is specified, all configs in scripts/comparator/ are run.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
cd "$PROJECT_DIR"

CONFIG_DIR="$SCRIPT_DIR/comparator"

# Find comparator binary
if [ -n "$COMPARATOR_BIN" ]; then
    COMPARATOR="$COMPARATOR_BIN"
elif command -v comparator &> /dev/null; then
    COMPARATOR="comparator"
else
    echo "ERROR: comparator binary not found."
    echo ""
    echo "Please either:"
    echo "  1. Install comparator and add to PATH"
    echo "  2. Set COMPARATOR_BIN environment variable"
    echo ""
    echo "To build comparator:"
    echo "  git clone https://github.com/leanprover/comparator.git"
    echo "  cd comparator && lake build"
    echo "  export COMPARATOR_BIN=\$(pwd)/.lake/build/bin/comparator"
    exit 1
fi

# Check for landrun
if ! command -v landrun &> /dev/null; then
    echo "WARNING: landrun not found in PATH."
    echo "Comparator requires landrun for sandboxed verification."
    echo ""
    echo "To install landrun:"
    echo "  git clone https://github.com/Zouuup/landrun.git"
    echo "  cd landrun && go build -o landrun ."
    echo "  sudo mv landrun /usr/local/bin/"
    echo ""
fi

# Check for lean4export
if ! command -v lean4export &> /dev/null; then
    echo "WARNING: lean4export not found in PATH."
    echo "Comparator requires lean4export for proof export."
    echo ""
fi

echo "========================================="
echo "Comparator Verification"
echo "========================================="
echo "Comparator binary: $COMPARATOR"
echo "Config directory: $CONFIG_DIR"
echo ""

# Function to run a single verification
run_verification() {
    local config="$1"
    local name=$(basename "$config" .json)

    echo "-----------------------------------------"
    echo "Verifying: $name"
    echo "Config: $config"
    echo "-----------------------------------------"

    if lake env "$COMPARATOR" "$config"; then
        echo "PASSED: $name"
        return 0
    else
        echo "FAILED: $name"
        return 1
    fi
}

FAILED=0

if [ -n "$1" ]; then
    # Run specific config
    if [ -f "$1" ]; then
        run_verification "$1" || FAILED=1
    elif [ -f "$CONFIG_DIR/$1" ]; then
        run_verification "$CONFIG_DIR/$1" || FAILED=1
    elif [ -f "$CONFIG_DIR/$1.json" ]; then
        run_verification "$CONFIG_DIR/$1.json" || FAILED=1
    else
        echo "ERROR: Config file not found: $1"
        exit 1
    fi
else
    # Run all configs
    for config in "$CONFIG_DIR"/*.json; do
        if [ -f "$config" ]; then
            echo ""
            run_verification "$config" || FAILED=1
        fi
    done
fi

echo ""
echo "========================================="
if [ $FAILED -eq 0 ]; then
    echo "All comparator verifications passed!"
    exit 0
else
    echo "Some comparator verifications failed!"
    exit 1
fi
