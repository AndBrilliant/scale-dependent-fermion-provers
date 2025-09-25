"""
Golden ratio patterns in fermion mass hierarchies.

This module explores the mathematical relationship between the golden ratio
and geometric patterns observed in fermion mass ratios.
"""

import numpy as np
from typing import List, Dict, Tuple, Optional
# import matplotlib.pyplot as plt  # Optional plotting capability
from dataclasses import dataclass

# Mathematical constants
PHI = (1 + np.sqrt(5)) / 2  # Golden ratio
PHI_CONJUGATE = (1 - np.sqrt(5)) / 2  # Golden ratio conjugate

@dataclass
class GeometricSequence:
    """Represents a geometric sequence with ratio r."""
    initial_value: float
    ratio: float
    length: int
    
    def generate(self) -> List[float]:
        """Generate the geometric sequence."""
        return [self.initial_value * (self.ratio ** i) for i in range(self.length)]
    
    def ratios(self) -> List[float]:
        """Calculate ratios between consecutive terms."""
        sequence = self.generate()
        return [sequence[i+1] / sequence[i] for i in range(len(sequence) - 1)]

class GoldenRatioAnalysis:
    """Analysis tools for golden ratio patterns."""
    
    @staticmethod
    def fibonacci_sequence(n: int) -> List[int]:
        """Generate Fibonacci sequence of length n."""
        if n <= 0:
            return []
        elif n == 1:
            return [1]
        elif n == 2:
            return [1, 1]
        
        fib = [1, 1]
        for i in range(2, n):
            fib.append(fib[i-1] + fib[i-2])
        
        return fib
    
    @staticmethod
    def fibonacci_ratios(n: int) -> List[float]:
        """Calculate ratios of consecutive Fibonacci numbers."""
        fib = GoldenRatioAnalysis.fibonacci_sequence(n)
        if len(fib) < 2:
            return []
        
        return [fib[i+1] / fib[i] for i in range(len(fib) - 1)]
    
    @staticmethod
    def continued_fraction_phi(n_terms: int) -> float:
        """Calculate phi using continued fraction expansion."""
        if n_terms <= 0:
            return 1.0
        
        result = 1.0
        for _ in range(n_terms - 1):
            result = 1.0 + 1.0 / result
        
        return result
    
    @staticmethod
    def golden_spiral_points(n_points: int, scale: float = 1.0) -> Tuple[List[float], List[float]]:
        """Generate points on a golden spiral."""
        angles = np.linspace(0, 4 * np.pi, n_points)
        radii = [scale * (PHI ** (angle / (2 * np.pi))) for angle in angles]
        
        x_coords = [r * np.cos(theta) for r, theta in zip(radii, angles)]
        y_coords = [r * np.sin(theta) for r, theta in zip(radii, angles)]
        
        return x_coords, y_coords
    
    @staticmethod
    def test_golden_ratio_hypothesis(mass_ratios: List[float], 
                                   tolerance: float = 0.1) -> Dict[str, any]:
        """
        Test if mass ratios follow golden ratio pattern.
        
        Args:
            mass_ratios: List of mass ratios to test
            tolerance: Relative tolerance for matching
            
        Returns:
            Dictionary with test results
        """
        if not mass_ratios:
            return {"error": "No mass ratios provided"}
        
        # Calculate geometric mean
        geom_mean = np.prod(mass_ratios) ** (1.0 / len(mass_ratios))
        
        # Test against golden ratio
        phi_deviation = abs(geom_mean - PHI) / PHI
        
        # Test individual ratios
        individual_deviations = [abs(ratio - PHI) / PHI for ratio in mass_ratios]
        
        # Test against Fibonacci ratios
        fib_ratios = GoldenRatioAnalysis.fibonacci_ratios(len(mass_ratios) + 1)
        fib_deviations = []
        
        if len(fib_ratios) >= len(mass_ratios):
            for i, ratio in enumerate(mass_ratios):
                fib_dev = abs(ratio - fib_ratios[-(len(mass_ratios) - i)]) / fib_ratios[-(len(mass_ratios) - i)]
                fib_deviations.append(fib_dev)
        
        results = {
            "geometric_mean": geom_mean,
            "phi_deviation": phi_deviation,
            "matches_golden_ratio": phi_deviation < tolerance,
            "individual_deviations": individual_deviations,
            "fibonacci_deviations": fib_deviations,
            "mean_individual_deviation": np.mean(individual_deviations),
            "mean_fibonacci_deviation": np.mean(fib_deviations) if fib_deviations else float('inf')
        }
        
        return results

def analyze_critical_scaling(coupling_values: List[float], 
                           mass_ratios: List[List[float]],
                           critical_coupling: float) -> Dict[str, any]:
    """
    Analyze how geometric patterns emerge near critical coupling values.
    
    Args:
        coupling_values: List of gauge coupling values
        mass_ratios: Corresponding mass ratios for each coupling
        critical_coupling: Critical coupling value
        
    Returns:
        Analysis results showing geometric pattern emergence
    """
    if len(coupling_values) != len(mass_ratios):
        return {"error": "Mismatched array lengths"}
    
    results = {
        "coupling_values": coupling_values,
        "critical_coupling": critical_coupling,
        "geometric_patterns": []
    }
    
    for i, (g, ratios) in enumerate(zip(coupling_values, mass_ratios)):
        # Distance from critical coupling
        distance_from_critical = abs(g - critical_coupling) / critical_coupling
        
        # Analyze golden ratio pattern
        pattern_analysis = GoldenRatioAnalysis.test_golden_ratio_hypothesis(ratios)
        
        pattern_data = {
            "coupling": g,
            "distance_from_critical": distance_from_critical,
            "geometric_mean_ratio": pattern_analysis.get("geometric_mean", 0),
            "phi_deviation": pattern_analysis.get("phi_deviation", float('inf')),
            "matches_golden_ratio": pattern_analysis.get("matches_golden_ratio", False)
        }
        
        results["geometric_patterns"].append(pattern_data)
    
    # Find coupling closest to critical point
    min_distance_idx = min(range(len(coupling_values)), 
                          key=lambda i: abs(coupling_values[i] - critical_coupling))
    
    results["closest_to_critical"] = results["geometric_patterns"][min_distance_idx]
    
    return results

if __name__ == "__main__":
    print("Golden Ratio Pattern Analysis")
    print("=" * 40)
    
    # Test Fibonacci convergence to golden ratio
    print("Fibonacci ratio convergence to φ:")
    fib_ratios = GoldenRatioAnalysis.fibonacci_ratios(15)
    for i, ratio in enumerate(fib_ratios[-5:], start=len(fib_ratios)-4):
        deviation = abs(ratio - PHI) / PHI
        print(f"  F_{i+1}/F_{i} = {ratio:.6f}, deviation = {deviation:.2%}")
    
    # Example mass ratios (hypothetical)
    example_ratios = [1.618, 1.620, 1.615]  # Close to golden ratio
    
    print(f"\nTesting mass ratios: {example_ratios}")
    analysis = GoldenRatioAnalysis.test_golden_ratio_hypothesis(example_ratios)
    
    print(f"Geometric mean: {analysis['geometric_mean']:.4f}")
    print(f"φ deviation: {analysis['phi_deviation']:.1%}")
    print(f"Matches golden ratio: {analysis['matches_golden_ratio']}")
    
    # Critical coupling analysis example
    print(f"\nCritical coupling analysis:")
    couplings = [0.25, 0.30, 0.35, 0.40, 0.45]  # Critical at ~0.35
    ratios_list = [
        [1.2, 1.3],      # Far from critical
        [1.5, 1.6],      # Approaching critical  
        [1.618, 1.618],  # At critical (golden ratio)
        [1.7, 1.8],      # Past critical
        [2.0, 2.1]       # Far past critical
    ]
    
    critical_analysis = analyze_critical_scaling(couplings, ratios_list, 0.35)
    
    closest = critical_analysis["closest_to_critical"]
    print(f"Closest to critical: g = {closest['coupling']}")
    print(f"Geometric mean ratio: {closest['geometric_mean_ratio']:.4f}")
    print(f"φ deviation: {closest['phi_deviation']:.1%}")