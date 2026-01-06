#!/bin/bash
# Verification script for ArtificialTheorems
# 1. Runs lean4checker on all modules in ArtificialTheorems
# 2. Runs safe_verify on spec/impl pairs

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
cd "$PROJECT_DIR"

BUILD_LIB=".lake/build/lib/lean"

echo "========================================="
echo "Building project..."
echo "========================================="
lake build ArtificialTheorems ArtificialTheoremsSpec

echo ""
echo "========================================="
echo "Running lean4checker on ArtificialTheorems modules..."
echo "========================================="

# Find all .lean files in ArtificialTheorems and convert to module names
find ArtificialTheorems -name "*.lean" | while read -r file; do
    # Convert path to module name: ArtificialTheorems/Opt/SGD.lean -> ArtificialTheorems.Opt.SGD
    module=$(echo "$file" | sed 's/\.lean$//' | tr '/' '.')

    # Check if olean exists
    olean_path="$BUILD_LIB/$(echo "$file" | sed 's/\.lean$/.olean/')"
    if [[ -f "$olean_path" ]]; then
        echo "Checking: $module"
        lake exe lean4checker "$module"
    else
        echo "Skipping: $module (no olean found)"
    fi
done

echo ""
echo "========================================="
echo "Running safe_verify on spec/impl pairs..."
echo "========================================="

# Find all spec files and match with impl files
find ArtificialTheoremsSpec -name "*Spec.lean" | while read -r spec_file; do
    # Convert spec path to impl path:
    # ArtificialTheoremsSpec/Opt/RobbinsSiegmundSpec.lean -> ArtificialTheorems/Opt/RobbinsSiegmund.lean
    impl_file=$(echo "$spec_file" | sed 's/ArtificialTheoremsSpec/ArtificialTheorems/' | sed 's/Spec\.lean$/.lean/')

    # Convert to olean paths
    spec_olean="$BUILD_LIB/$(echo "$spec_file" | sed 's/\.lean$/.olean/')"
    impl_olean="$BUILD_LIB/$(echo "$impl_file" | sed 's/\.lean$/.olean/')"

    if [[ -f "$spec_olean" ]] && [[ -f "$impl_olean" ]]; then
        echo "Verifying: $(basename "$spec_file" .lean) against $(basename "$impl_file" .lean)"
        echo "  Spec: $spec_olean"
        echo "  Impl: $impl_olean"
        lake exe safe_verify "$spec_olean" "$impl_olean"
    else
        if [[ ! -f "$spec_olean" ]]; then
            echo "WARNING: Spec olean not found: $spec_olean"
        fi
        if [[ ! -f "$impl_olean" ]]; then
            echo "WARNING: Impl olean not found: $impl_olean"
        fi
    fi
done

echo ""
echo "========================================="
echo "Verification complete!"
echo "========================================="
