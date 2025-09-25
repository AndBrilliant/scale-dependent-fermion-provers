#!/usr/bin/env python3
"""
Example: Golden ratio analysis of fermion mass hierarchies.

This script demonstrates how to analyze Standard Model fermion masses
for golden ratio patterns and geometric relationships.
"""

import sys
from pathlib import Path

# Add mathematical_models to path
project_root = Path(__file__).parent.parent
sys.path.append(str(project_root / "mathematical_models" / "fermion_mass_hierarchies"))
sys.path.append(str(project_root / "mathematical_models" / "geometric_patterns"))

try:
    from standard_model_masses import (
        MassHierarchy, FermionType, golden_ratio_hypothesis, STANDARD_MODEL_MASSES
    )
    from golden_ratio_patterns import GoldenRatioAnalysis, PHI
except ImportError as e:
    print(f"Import error: {e}")
    print("Make sure you're running from the project root directory")
    sys.exit(1)

def main():
    """Demonstrate golden ratio analysis of fermion masses."""
    
    print("=" * 60)
    print("GOLDEN RATIO ANALYSIS OF FERMION MASS HIERARCHIES")
    print("=" * 60)
    
    print(f"Golden ratio φ = {PHI:.6f}")
    print()
    
    # Analyze each fermion sector
    fermion_types = [
        (FermionType.QUARK_UP, "UP-TYPE QUARKS"),
        (FermionType.QUARK_DOWN, "DOWN-TYPE QUARKS"), 
        (FermionType.LEPTON_CHARGED, "CHARGED LEPTONS")
    ]
    
    for fermion_type, sector_name in fermion_types:
        print(f"{sector_name}:")
        print("-" * len(sector_name))
        
        # Get fermions in this sector
        fermions = MassHierarchy.get_masses_by_type(fermion_type)
        
        # Display masses
        for fermion in fermions:
            print(f"  {fermion.name:8s}: {fermion.mass_gev:12.6e} GeV")
        
        # Calculate mass ratios
        ratios = MassHierarchy.mass_ratios(fermions)
        print(f"  Ratios: {[f'{r:.3f}' for r in ratios]}")
        
        # Analyze geometric properties
        geom_mean = MassHierarchy.geometric_mean_ratio(fermions)
        hierarchy_strength = MassHierarchy.hierarchy_strength(fermions)
        
        print(f"  Geometric mean ratio: {geom_mean:.4f}")
        print(f"  Hierarchy strength:   {hierarchy_strength:.2f} orders of magnitude")
        
        # Test golden ratio hypothesis
        phi_analysis = GoldenRatioAnalysis.test_golden_ratio_hypothesis(ratios)
        phi_deviation = phi_analysis["phi_deviation"]
        matches_phi = phi_analysis["matches_golden_ratio"]
        
        print(f"  φ deviation:          {phi_deviation:.1%}")
        print(f"  Golden ratio-like:    {'Yes' if matches_phi else 'No'}")
        print()
    
    # Overall golden ratio hypothesis test
    print("OVERALL GOLDEN RATIO HYPOTHESIS TEST:")
    print("-" * 40)
    
    golden_results = golden_ratio_hypothesis()
    
    for sector, result in golden_results.items():
        deviation = result["golden_ratio_deviation"] 
        is_golden = result["is_golden_like"]
        geom_mean = result["geometric_mean_ratio"]
        
        status = "✓" if is_golden else "✗"
        print(f"{status} {sector.replace('_', ' ').title():<20}: "
              f"ratio={geom_mean:.4f}, deviation={deviation:.1%}")
    
    # Fibonacci convergence demonstration
    print(f"\nFIBONACCI CONVERGENCE TO φ:")
    print("-" * 30)
    
    fib_ratios = GoldenRatioAnalysis.fibonacci_ratios(15)
    print("Last few Fibonacci ratios:")
    for i, ratio in enumerate(fib_ratios[-5:], start=len(fib_ratios)-4):
        deviation = abs(ratio - PHI) / PHI
        print(f"  F_{i+2}/F_{i+1} = {ratio:.6f}, deviation = {deviation:.2%}")
    
    # Critical coupling hypothesis
    print(f"\nCRITICAL COUPLING HYPOTHESIS:")
    print("-" * 32)
    print("If geometric patterns emerge at critical gauge couplings,")
    print("we expect mass ratios to approach φ as g² → 4π.")
    print(f"Critical value: g² = 4π ≈ {4 * 3.14159:.3f}")
    
    # Summary
    golden_sectors = [s for s, r in golden_results.items() if r["is_golden_like"]]
    print(f"\nSUMMARY:")
    print(f"  Sectors showing golden ratio patterns: {len(golden_sectors)}/3")
    if golden_sectors:
        print(f"  Golden ratio sectors: {', '.join(s.replace('_', ' ').title() for s in golden_sectors)}")
    
    print("\nThis analysis suggests geometric patterns in fermion mass hierarchies")
    print("that may be related to critical phenomena in gauge theories.")

if __name__ == "__main__":
    main()