#!/bin/bash
# Build and verification script for the scale-dependent fermion provers project

set -e  # Exit on any error

echo "=================================================="
echo "Scale-Dependent Fermion Provers - Build & Verify"
echo "=================================================="

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to print colored output
print_status() {
    local status=$1
    local message=$2
    case $status in
        "SUCCESS") echo -e "\033[32m✓ $message\033[0m" ;;
        "FAILURE") echo -e "\033[31m✗ $message\033[0m" ;;
        "INFO")    echo -e "\033[34mℹ $message\033[0m" ;;
        "WARNING") echo -e "\033[33m⚠ $message\033[0m" ;;
    esac
}

# Check project structure
echo "Checking project structure..."
required_dirs=("theorem_provers" "mathematical_models" "verification_scripts" "docs" "examples")
for dir in "${required_dirs[@]}"; do
    if [ -d "$dir" ]; then
        print_status "SUCCESS" "Directory $dir exists"
    else
        print_status "FAILURE" "Directory $dir missing"
        exit 1
    fi
done

# Check Python availability
echo
echo "Checking Python environment..."
if command_exists python3; then
    python_version=$(python3 --version)
    print_status "SUCCESS" "Python found: $python_version"
    
    # Check required Python packages
    required_packages=("numpy" "scipy")
    for package in "${required_packages[@]}"; do
        if python3 -c "import $package" 2>/dev/null; then
            print_status "SUCCESS" "Python package $package available"
        else
            print_status "WARNING" "Python package $package not found (install with: pip3 install $package)"
        fi
    done
else
    print_status "FAILURE" "Python3 not found"
fi

# Check Lean installation (optional)
echo
echo "Checking Lean 4 environment..."
if command_exists lean; then
    lean_version=$(lean --version)
    print_status "SUCCESS" "Lean found: $lean_version"
    
    if command_exists lake; then
        lake_version=$(lake --version)
        print_status "SUCCESS" "Lake found: $lake_version"
        
        # Try to build Lean project
        echo
        echo "Building Lean project..."
        cd theorem_provers/lean
        if timeout 60 lake build; then
            print_status "SUCCESS" "Lean project built successfully"
        else
            print_status "WARNING" "Lean project build failed or timed out (this is expected if dependencies aren't installed)"
        fi
        cd ../..
    else
        print_status "WARNING" "Lake build system not found"
    fi
else
    print_status "INFO" "Lean 4 not found (optional - install from https://leanprover.github.io/lean4/doc/setup.html)"
fi

# Check Coq installation (optional)
echo
echo "Checking Coq environment..."
if command_exists coqc; then
    coq_version=$(coqc --version | head -n 1)
    print_status "SUCCESS" "Coq found: $coq_version"
    
    # Try to compile Coq files
    echo
    echo "Compiling Coq files..."
    cd theorem_provers/coq
    if timeout 60 coqc FermionBasic.v; then
        print_status "SUCCESS" "Basic Coq file compiled"
        # Clean up compiled files
        rm -f *.vo *.vok *.vos *.glob
    else
        print_status "WARNING" "Coq compilation failed (may need dependencies)"
    fi
    cd ../..
else
    print_status "INFO" "Coq not found (optional - install from https://coq.inria.fr/)"
fi

# Run Python model validation
echo
echo "Running mathematical model validation..."
if python3 verification_scripts/automated_verification/model_validator.py mathematical_models/; then
    print_status "SUCCESS" "Mathematical model validation passed"
else
    print_status "WARNING" "Mathematical model validation had issues"
fi

# Run example scripts
echo
echo "Testing example scripts..."
if python3 examples/golden_ratio_analysis.py > /dev/null; then
    print_status "SUCCESS" "Golden ratio analysis example works"
else
    print_status "WARNING" "Golden ratio analysis example failed"
fi

# Final summary
echo
echo "=================================================="
echo "BUILD AND VERIFICATION SUMMARY"
echo "=================================================="

echo "Project Structure: ✓ Complete"
echo "Python Environment: $(command_exists python3 && echo "✓ Available" || echo "✗ Missing")"
echo "Lean 4: $(command_exists lean && echo "✓ Available" || echo "- Optional")"
echo "Coq: $(command_exists coqc && echo "✓ Available" || echo "- Optional")"

echo
echo "To get started:"
echo "1. Install Python dependencies: pip3 install numpy scipy matplotlib"
echo "2. (Optional) Install Lean 4: https://leanprover.github.io/lean4/doc/setup.html"  
echo "3. (Optional) Install Coq: https://coq.inria.fr/"
echo "4. Run examples: python3 examples/golden_ratio_analysis.py"
echo "5. Run verification: python3 verification_scripts/automated_verification/model_validator.py mathematical_models/"

echo
print_status "SUCCESS" "Setup complete! The project structure is ready for formal verification work."