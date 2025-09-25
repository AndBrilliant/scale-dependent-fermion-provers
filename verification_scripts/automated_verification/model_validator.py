#!/usr/bin/env python3
"""
Mathematical model validation for fermion mass hierarchy theories.

This script validates the mathematical consistency and physical reasonableness
of the models implemented in the project.
"""

import numpy as np
import sys
import importlib.util
from pathlib import Path
from typing import Dict, List, Any, Optional, Callable
import traceback
import json
import time

class ModelValidator:
    """Validator for mathematical models in the project."""
    
    def __init__(self, models_root: str):
        """
        Initialize validator with models directory.
        
        Args:
            models_root: Path to mathematical_models directory
        """
        self.models_root = Path(models_root)
        self.validation_results = {}
        self.tolerance = 1e-10  # Numerical tolerance for comparisons
    
    def find_python_models(self) -> List[Path]:
        """Find all Python model files."""
        python_files = []
        for py_file in self.models_root.rglob("*.py"):
            if not py_file.name.startswith("__") and py_file.name != "__init__.py":
                python_files.append(py_file)
        return sorted(python_files)
    
    def load_module(self, module_path: Path) -> Optional[Any]:
        """
        Dynamically load a Python module.
        
        Args:
            module_path: Path to Python file
            
        Returns:
            Loaded module or None if loading failed
        """
        try:
            spec = importlib.util.spec_from_file_location(
                module_path.stem, module_path
            )
            if spec is None or spec.loader is None:
                return None
            
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return module
            
        except Exception as e:
            print(f"Failed to load {module_path}: {e}")
            return None
    
    def validate_rg_flow(self) -> Dict[str, Any]:
        """Validate renormalization group flow implementation."""
        validation_result = {
            "test_name": "RG Flow Validation",
            "success": True,
            "tests": [],
            "errors": []
        }
        
        try:
            # Load RG module
            rg_path = self.models_root / "scale_dependent_theories" / "renormalization_group.py"
            if not rg_path.exists():
                validation_result["success"] = False
                validation_result["errors"].append("RG module not found")
                return validation_result
            
            rg_module = self.load_module(rg_path)
            if rg_module is None:
                validation_result["success"] = False
                validation_result["errors"].append("Failed to load RG module")
                return validation_result
            
            # Test 1: Beta function sign consistency
            test_result = {"name": "Beta function signs", "passed": True, "details": ""}
            
            # For QED, beta function should be positive (asymptotic freedom violation)
            g_test = 0.3
            beta_g = rg_module.gauge_coupling_beta(g_test)
            
            if beta_g <= 0:
                test_result["passed"] = False
                test_result["details"] = f"QED beta function should be positive, got {beta_g}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
            # Test 2: RG flow integration
            test_result = {"name": "RG flow integration", "passed": True, "details": ""}
            
            try:
                beta_funcs = {
                    'g': rg_module.gauge_coupling_beta,
                    'm': rg_module.fermion_mass_beta
                }
                rg_flow = rg_module.RGFlow(beta_funcs)
                
                initial = {'g': 0.1, 'm': 0.01}
                solution = rg_flow.solve(initial, (0, 1), 50)
                
                if not solution['success']:
                    test_result["passed"] = False
                    test_result["details"] = "RG flow integration failed"
                    validation_result["success"] = False
                elif len(solution['g']) == 0:
                    test_result["passed"] = False
                    test_result["details"] = "Empty solution returned"
                    validation_result["success"] = False
                
            except Exception as e:
                test_result["passed"] = False
                test_result["details"] = f"RG integration error: {str(e)}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
            # Test 3: Physical reasonableness
            test_result = {"name": "Physical constraints", "passed": True, "details": ""}
            
            # Gauge coupling should remain positive
            if 'g' in solution and solution['success']:
                g_values = solution['g']
                if np.any(g_values <= 0):
                    test_result["passed"] = False
                    test_result["details"] = "Gauge coupling became non-positive"
                    validation_result["success"] = False
                
                # Check for runaway behavior (coupling becoming too large)
                if np.any(g_values > 10):
                    test_result["passed"] = False
                    test_result["details"] = "Gauge coupling grew too large (>10)"
                    validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
        except Exception as e:
            validation_result["success"] = False
            validation_result["errors"].append(f"Unexpected error: {str(e)}")
            validation_result["errors"].append(traceback.format_exc())
        
        return validation_result
    
    def validate_mass_hierarchies(self) -> Dict[str, Any]:
        """Validate fermion mass hierarchy models."""
        validation_result = {
            "test_name": "Mass Hierarchy Validation",
            "success": True,
            "tests": [],
            "errors": []
        }
        
        try:
            # Load mass hierarchy module
            mass_path = self.models_root / "fermion_mass_hierarchies" / "standard_model_masses.py"
            if not mass_path.exists():
                validation_result["success"] = False
                validation_result["errors"].append("Mass hierarchy module not found")
                return validation_result
            
            mass_module = self.load_module(mass_path)
            if mass_module is None:
                validation_result["success"] = False
                validation_result["errors"].append("Failed to load mass hierarchy module")
                return validation_result
            
            # Test 1: Mass data consistency
            test_result = {"name": "Mass data consistency", "passed": True, "details": ""}
            
            masses = mass_module.STANDARD_MODEL_MASSES
            
            # Check that all masses are positive
            for name, mass_data in masses.items():
                if mass_data.mass_gev <= 0:
                    test_result["passed"] = False
                    test_result["details"] = f"Non-positive mass for {name}: {mass_data.mass_gev}"
                    validation_result["success"] = False
                    break
            
            # Check generation ordering
            generations = [1, 2, 3]
            for gen in generations:
                gen_masses = [m for m in masses.values() if m.generation == gen]
                if len(gen_masses) == 0:
                    test_result["passed"] = False
                    test_result["details"] = f"No masses found for generation {gen}"
                    validation_result["success"] = False
                    break
            
            validation_result["tests"].append(test_result)
            
            # Test 2: Hierarchy analysis
            test_result = {"name": "Hierarchy analysis", "passed": True, "details": ""}
            
            try:
                # Test charged lepton hierarchy
                lepton_analysis = mass_module.MassHierarchy.analyze_sector(
                    mass_module.FermionType.LEPTON_CHARGED
                )
                
                if "error" in lepton_analysis:
                    test_result["passed"] = False
                    test_result["details"] = f"Lepton analysis error: {lepton_analysis['error']}"
                    validation_result["success"] = False
                else:
                    # Check that hierarchy strength is reasonable (should be > 0)
                    if lepton_analysis.get("hierarchy_strength", 0) <= 0:
                        test_result["passed"] = False
                        test_result["details"] = "Invalid hierarchy strength"
                        validation_result["success"] = False
                
            except Exception as e:
                test_result["passed"] = False
                test_result["details"] = f"Hierarchy analysis error: {str(e)}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
            # Test 3: Golden ratio hypothesis
            test_result = {"name": "Golden ratio hypothesis", "passed": True, "details": ""}
            
            try:
                golden_results = mass_module.golden_ratio_hypothesis()
                
                # Should return results for each fermion type
                expected_types = [
                    mass_module.FermionType.QUARK_UP.value,
                    mass_module.FermionType.QUARK_DOWN.value,
                    mass_module.FermionType.LEPTON_CHARGED.value
                ]
                
                for fermion_type in expected_types:
                    if fermion_type not in golden_results:
                        test_result["passed"] = False
                        test_result["details"] = f"Missing golden ratio analysis for {fermion_type}"
                        validation_result["success"] = False
                        break
                
            except Exception as e:
                test_result["passed"] = False
                test_result["details"] = f"Golden ratio test error: {str(e)}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
        except Exception as e:
            validation_result["success"] = False
            validation_result["errors"].append(f"Unexpected error: {str(e)}")
            validation_result["errors"].append(traceback.format_exc())
        
        return validation_result
    
    def validate_geometric_patterns(self) -> Dict[str, Any]:
        """Validate geometric pattern models."""
        validation_result = {
            "test_name": "Geometric Pattern Validation",
            "success": True,
            "tests": [],
            "errors": []
        }
        
        try:
            # Load geometric patterns module
            pattern_path = self.models_root / "geometric_patterns" / "golden_ratio_patterns.py"
            if not pattern_path.exists():
                validation_result["success"] = False
                validation_result["errors"].append("Geometric patterns module not found")
                return validation_result
            
            pattern_module = self.load_module(pattern_path)
            if pattern_module is None:
                validation_result["success"] = False
                validation_result["errors"].append("Failed to load geometric patterns module")
                return validation_result
            
            # Test 1: Golden ratio constant
            test_result = {"name": "Golden ratio value", "passed": True, "details": ""}
            
            phi = pattern_module.PHI
            expected_phi = (1 + np.sqrt(5)) / 2
            
            if abs(phi - expected_phi) > self.tolerance:
                test_result["passed"] = False
                test_result["details"] = f"Golden ratio value incorrect: {phi} vs {expected_phi}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
            # Test 2: Fibonacci sequence and ratios
            test_result = {"name": "Fibonacci convergence", "passed": True, "details": ""}
            
            try:
                fib_ratios = pattern_module.GoldenRatioAnalysis.fibonacci_ratios(20)
                
                if len(fib_ratios) == 0:
                    test_result["passed"] = False
                    test_result["details"] = "No Fibonacci ratios generated"
                    validation_result["success"] = False
                else:
                    # Last few ratios should converge to golden ratio
                    last_ratio = fib_ratios[-1]
                    if abs(last_ratio - phi) > 0.01:  # 1% tolerance for convergence
                        test_result["passed"] = False
                        test_result["details"] = f"Fibonacci ratios don't converge to φ: {last_ratio}"
                        validation_result["success"] = False
                
            except Exception as e:
                test_result["passed"] = False
                test_result["details"] = f"Fibonacci test error: {str(e)}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
            # Test 3: Golden ratio hypothesis testing
            test_result = {"name": "Golden ratio hypothesis test", "passed": True, "details": ""}
            
            try:
                # Test with perfect golden ratio
                perfect_ratios = [phi, phi, phi]
                analysis = pattern_module.GoldenRatioAnalysis.test_golden_ratio_hypothesis(perfect_ratios, 0.001)
                
                if not analysis.get("matches_golden_ratio", False):
                    test_result["passed"] = False
                    test_result["details"] = "Perfect golden ratios not recognized as matching"
                    validation_result["success"] = False
                
                # Test with non-golden ratios
                non_golden_ratios = [2.0, 2.0, 2.0]
                analysis2 = pattern_module.GoldenRatioAnalysis.test_golden_ratio_hypothesis(non_golden_ratios, 0.1)
                
                if analysis2.get("matches_golden_ratio", True):
                    test_result["passed"] = False
                    test_result["details"] = "Non-golden ratios incorrectly identified as golden"
                    validation_result["success"] = False
                
            except Exception as e:
                test_result["passed"] = False
                test_result["details"] = f"Hypothesis test error: {str(e)}"
                validation_result["success"] = False
            
            validation_result["tests"].append(test_result)
            
        except Exception as e:
            validation_result["success"] = False
            validation_result["errors"].append(f"Unexpected error: {str(e)}")
            validation_result["errors"].append(traceback.format_exc())
        
        return validation_result
    
    def run_all_validations(self) -> Dict[str, Any]:
        """Run all model validations."""
        print("Starting mathematical model validation...")
        start_time = time.time()
        
        # Run individual validations
        validations = [
            self.validate_rg_flow,
            self.validate_mass_hierarchies,
            self.validate_geometric_patterns
        ]
        
        results = []
        overall_success = True
        
        for validation_func in validations:
            print(f"Running {validation_func.__name__}...")
            result = validation_func()
            results.append(result)
            if not result["success"]:
                overall_success = False
        
        end_time = time.time()
        
        # Compile overall report
        total_tests = sum(len(r["tests"]) for r in results)
        passed_tests = sum(len([t for t in r["tests"] if t["passed"]]) for r in results)
        
        report = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "duration_seconds": end_time - start_time,
            "overall_success": overall_success,
            "summary": {
                "total_validations": len(results),
                "successful_validations": len([r for r in results if r["success"]]),
                "total_tests": total_tests,
                "passed_tests": passed_tests
            },
            "validation_results": results
        }
        
        self.validation_results = report
        return report
    
    def generate_report(self, output_file: Optional[str] = None) -> str:
        """Generate human-readable validation report."""
        if not self.validation_results:
            return "No validation results available. Run run_all_validations() first."
        
        results = self.validation_results
        
        report_lines = [
            "MATHEMATICAL MODEL VALIDATION REPORT",
            "=" * 55,
            f"Timestamp: {results['timestamp']}",
            f"Duration: {results['duration_seconds']:.2f} seconds",
            "",
            f"OVERALL STATUS: {'✓ PASSED' if results['overall_success'] else '✗ FAILED'}",
            "",
            "SUMMARY:",
            f"  Validations: {results['summary']['successful_validations']}/{results['summary']['total_validations']}",
            f"  Tests: {results['summary']['passed_tests']}/{results['summary']['total_tests']}",
            f"  Success rate: {results['summary']['passed_tests'] / max(1, results['summary']['total_tests']) * 100:.1f}%",
            ""
        ]
        
        # Detailed results for each validation
        for validation in results["validation_results"]:
            status = "✓ PASSED" if validation["success"] else "✗ FAILED"
            report_lines.append(f"{validation['test_name']}: {status}")
            
            for test in validation["tests"]:
                test_status = "✓" if test["passed"] else "✗"
                report_lines.append(f"  {test_status} {test['name']}")
                if not test["passed"] and test["details"]:
                    report_lines.append(f"    {test['details']}")
            
            if validation["errors"]:
                for error in validation["errors"]:
                    report_lines.append(f"  ERROR: {error}")
            
            report_lines.append("")
        
        report_text = '\n'.join(report_lines)
        
        if output_file:
            with open(output_file, 'w') as f:
                f.write(report_text)
            print(f"Report written to {output_file}")
        
        return report_text

def main():
    """Main entry point for command line usage."""
    if len(sys.argv) < 2:
        print("Usage: python model_validator.py <mathematical_models_root>")
        sys.exit(1)
    
    models_root = sys.argv[1]
    
    if not Path(models_root).exists():
        print(f"Error: Models root '{models_root}' does not exist")
        sys.exit(1)
    
    validator = ModelValidator(models_root)
    
    # Run all validations
    results = validator.run_all_validations()
    
    # Generate and display report
    report = validator.generate_report("model_validation_report.txt")
    print("\n" + report)
    
    # Save detailed results as JSON
    with open("model_validation_results.json", "w") as f:
        json.dump(results, f, indent=2)
    
    # Exit with error code if validation failed
    if not results["overall_success"]:
        sys.exit(1)

if __name__ == "__main__":
    main()