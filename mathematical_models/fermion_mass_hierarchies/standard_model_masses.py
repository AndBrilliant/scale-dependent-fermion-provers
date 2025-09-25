"""
Standard Model fermion masses and their hierarchical patterns.

This module contains experimental data for fermion masses and provides
tools for analyzing mass hierarchies and ratios.
"""

import numpy as np
from typing import Dict, List, Tuple
from dataclasses import dataclass
from enum import Enum

class FermionType(Enum):
    """Enumeration of fermion types."""
    QUARK_UP = "up_quark"
    QUARK_DOWN = "down_quark"
    LEPTON_CHARGED = "charged_lepton"
    LEPTON_NEUTRINO = "neutrino"

@dataclass
class FermionMass:
    """Represents a fermion mass with metadata."""
    name: str
    mass_gev: float  # Mass in GeV
    generation: int  # 1, 2, or 3
    fermion_type: FermionType
    uncertainty: float = 0.0  # Relative uncertainty

# Standard Model fermion masses (approximate values in GeV)
STANDARD_MODEL_MASSES = {
    # Up-type quarks
    "u": FermionMass("up", 2.2e-3, 1, FermionType.QUARK_UP, 0.5),
    "c": FermionMass("charm", 1.275, 2, FermionType.QUARK_UP, 0.02),
    "t": FermionMass("top", 173.1, 3, FermionType.QUARK_UP, 0.005),
    
    # Down-type quarks  
    "d": FermionMass("down", 4.7e-3, 1, FermionType.QUARK_DOWN, 0.2),
    "s": FermionMass("strange", 0.093, 2, FermionType.QUARK_DOWN, 0.1),
    "b": FermionMass("bottom", 4.18, 3, FermionType.QUARK_DOWN, 0.01),
    
    # Charged leptons
    "e": FermionMass("electron", 0.511e-3, 1, FermionType.LEPTON_CHARGED, 1e-8),
    "μ": FermionMass("muon", 0.1057, 2, FermionType.LEPTON_CHARGED, 1e-6),
    "τ": FermionMass("tau", 1.777, 3, FermionType.LEPTON_CHARGED, 1e-4),
}

class MassHierarchy:
    """Analysis tools for fermion mass hierarchies."""
    
    @staticmethod
    def get_masses_by_type(fermion_type: FermionType) -> List[FermionMass]:
        """Get all fermions of a specific type, sorted by generation."""
        masses = [m for m in STANDARD_MODEL_MASSES.values() 
                 if m.fermion_type == fermion_type]
        return sorted(masses, key=lambda x: x.generation)
    
    @staticmethod
    def mass_ratios(fermions: List[FermionMass]) -> List[float]:
        """Calculate mass ratios between consecutive generations."""
        if len(fermions) < 2:
            return []
        
        ratios = []
        for i in range(len(fermions) - 1):
            ratio = fermions[i+1].mass_gev / fermions[i].mass_gev
            ratios.append(ratio)
        
        return ratios
    
    @staticmethod
    def geometric_mean_ratio(fermions: List[FermionMass]) -> float:
        """Calculate geometric mean of mass ratios."""
        ratios = MassHierarchy.mass_ratios(fermions)
        if not ratios:
            return 1.0
        
        product = np.prod(ratios)
        return product ** (1.0 / len(ratios))
    
    @staticmethod
    def hierarchy_strength(fermions: List[FermionMass]) -> float:
        """Measure hierarchy strength as log(max_mass/min_mass)."""
        if len(fermions) < 2:
            return 0.0
        
        masses = [f.mass_gev for f in fermions]
        return np.log10(max(masses) / min(masses))
    
    @staticmethod
    def analyze_sector(fermion_type: FermionType) -> Dict[str, float]:
        """Comprehensive analysis of a fermion sector."""
        fermions = MassHierarchy.get_masses_by_type(fermion_type)
        
        if len(fermions) < 2:
            return {"error": "Insufficient data"}
        
        ratios = MassHierarchy.mass_ratios(fermions)
        
        analysis = {
            "num_generations": len(fermions),
            "mass_ratios": ratios,
            "geometric_mean_ratio": MassHierarchy.geometric_mean_ratio(fermions),
            "hierarchy_strength": MassHierarchy.hierarchy_strength(fermions),
            "heaviest_mass": max(f.mass_gev for f in fermions),
            "lightest_mass": min(f.mass_gev for f in fermions),
        }
        
        return analysis

def golden_ratio_hypothesis():
    """
    Test if fermion mass ratios are related to the golden ratio.
    
    Returns:
        Dictionary with analysis results
    """
    golden_ratio = (1 + np.sqrt(5)) / 2
    results = {}
    
    for fermion_type in FermionType:
        analysis = MassHierarchy.analyze_sector(fermion_type)
        
        if "error" not in analysis:
            ratios = analysis["mass_ratios"]
            
            # Check if geometric mean is close to golden ratio
            geom_mean = analysis["geometric_mean_ratio"]
            golden_deviation = abs(geom_mean - golden_ratio) / golden_ratio
            
            results[fermion_type.value] = {
                "geometric_mean_ratio": geom_mean,
                "golden_ratio_deviation": golden_deviation,
                "is_golden_like": golden_deviation < 0.1,  # Within 10%
                "individual_ratios": ratios
            }
    
    return results

if __name__ == "__main__":
    print("Standard Model Fermion Mass Analysis")
    print("=" * 50)
    
    # Analyze each fermion sector
    for fermion_type in [FermionType.QUARK_UP, FermionType.QUARK_DOWN, 
                        FermionType.LEPTON_CHARGED]:
        print(f"\n{fermion_type.value.upper()} SECTOR:")
        analysis = MassHierarchy.analyze_sector(fermion_type)
        
        if "error" not in analysis:
            print(f"  Mass ratios: {[f'{r:.2f}' for r in analysis['mass_ratios']]}")
            print(f"  Geometric mean ratio: {analysis['geometric_mean_ratio']:.3f}")
            print(f"  Hierarchy strength: {analysis['hierarchy_strength']:.2f} orders")
    
    # Test golden ratio hypothesis
    print("\n\nGOLDEN RATIO HYPOTHESIS:")
    print("=" * 30)
    golden_results = golden_ratio_hypothesis()
    golden_ratio = (1 + np.sqrt(5)) / 2
    print(f"Golden ratio φ = {golden_ratio:.6f}")
    
    for sector, result in golden_results.items():
        deviation = result["golden_ratio_deviation"]
        is_golden = result["is_golden_like"]
        print(f"{sector}: deviation = {deviation:.1%}, golden-like = {is_golden}")