#!/usr/bin/env python3
"""
Automated Lean proof verification for fermion mass hierarchy theorems.

This script provides automated checking of Lean proofs and reports
verification status for all theorems in the project.
"""

import subprocess
import os
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import json
import time

class LeanVerifier:
    """Automated verification of Lean proofs."""
    
    def __init__(self, project_root: str):
        """
        Initialize verifier with project root directory.
        
        Args:
            project_root: Path to Lean project root containing lakefile.lean
        """
        self.project_root = Path(project_root)
        self.lean_files = []
        self.verification_results = {}
    
    def find_lean_files(self) -> List[Path]:
        """Find all .lean files in the project."""
        lean_files = []
        for lean_file in self.project_root.rglob("*.lean"):
            if not lean_file.name.startswith("."):
                lean_files.append(lean_file)
        
        self.lean_files = sorted(lean_files)
        return self.lean_files
    
    def check_lake_installation(self) -> bool:
        """Check if Lake (Lean build system) is installed."""
        try:
            result = subprocess.run(
                ["lake", "--version"], 
                capture_output=True, text=True, timeout=10
            )
            return result.returncode == 0
        except (subprocess.TimeoutExpired, FileNotFoundError):
            return False
    
    def build_project(self) -> Tuple[bool, str]:
        """
        Build the entire Lean project.
        
        Returns:
            Tuple of (success, output_message)
        """
        if not self.check_lake_installation():
            return False, "Lake (Lean build system) not found. Please install Lean 4."
        
        try:
            # Change to project directory
            original_cwd = os.getcwd()
            os.chdir(self.project_root)
            
            # Run lake build
            result = subprocess.run(
                ["lake", "build"],
                capture_output=True, 
                text=True, 
                timeout=300  # 5 minute timeout
            )
            
            os.chdir(original_cwd)
            
            success = result.returncode == 0
            output = result.stdout + result.stderr
            
            return success, output
            
        except subprocess.TimeoutExpired:
            os.chdir(original_cwd)
            return False, "Build timeout after 5 minutes"
        except Exception as e:
            os.chdir(original_cwd)
            return False, f"Build error: {str(e)}"
    
    def verify_file(self, lean_file: Path) -> Dict[str, any]:
        """
        Verify a single Lean file.
        
        Args:
            lean_file: Path to .lean file
            
        Returns:
            Dictionary with verification results
        """
        if not self.check_lake_installation():
            return {
                "file": str(lean_file),
                "success": False,
                "error": "Lake not installed"
            }
        
        try:
            original_cwd = os.getcwd()
            os.chdir(self.project_root)
            
            # Use lake to check the specific file
            result = subprocess.run(
                ["lake", "env", "lean", str(lean_file.relative_to(self.project_root))],
                capture_output=True,
                text=True,
                timeout=120  # 2 minute timeout per file
            )
            
            os.chdir(original_cwd)
            
            verification_result = {
                "file": str(lean_file.relative_to(self.project_root)),
                "success": result.returncode == 0,
                "stdout": result.stdout,
                "stderr": result.stderr,
                "return_code": result.returncode
            }
            
            # Parse for specific error types
            if not verification_result["success"]:
                stderr = result.stderr.lower()
                if "sorry" in stderr:
                    verification_result["has_sorry"] = True
                if "error" in stderr:
                    verification_result["has_errors"] = True
                if "warning" in stderr:
                    verification_result["has_warnings"] = True
            
            return verification_result
            
        except subprocess.TimeoutExpired:
            os.chdir(original_cwd)
            return {
                "file": str(lean_file.relative_to(self.project_root)),
                "success": False,
                "error": "Verification timeout"
            }
        except Exception as e:
            os.chdir(original_cwd)
            return {
                "file": str(lean_file.relative_to(self.project_root)),
                "success": False,
                "error": str(e)
            }
    
    def verify_all_files(self) -> Dict[str, any]:
        """
        Verify all Lean files in the project.
        
        Returns:
            Complete verification report
        """
        print("Starting Lean project verification...")
        start_time = time.time()
        
        # Find all Lean files
        self.find_lean_files()
        print(f"Found {len(self.lean_files)} Lean files")
        
        # First, try to build the entire project
        print("Building project...")
        build_success, build_output = self.build_project()
        
        # Verify individual files
        file_results = []
        for i, lean_file in enumerate(self.lean_files, 1):
            print(f"Verifying file {i}/{len(self.lean_files)}: {lean_file.name}")
            result = self.verify_file(lean_file)
            file_results.append(result)
        
        end_time = time.time()
        
        # Compile results
        successful_files = [r for r in file_results if r["success"]]
        failed_files = [r for r in file_results if not r["success"]]
        
        report = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "duration_seconds": end_time - start_time,
            "project_build": {
                "success": build_success,
                "output": build_output
            },
            "files": {
                "total": len(self.lean_files),
                "successful": len(successful_files),
                "failed": len(failed_files)
            },
            "file_results": file_results,
            "summary": {
                "all_files_verified": len(failed_files) == 0,
                "project_builds": build_success
            }
        }
        
        self.verification_results = report
        return report
    
    def generate_report(self, output_file: Optional[str] = None) -> str:
        """
        Generate a human-readable verification report.
        
        Args:
            output_file: Optional file to write report to
            
        Returns:
            Report string
        """
        if not self.verification_results:
            return "No verification results available. Run verify_all_files() first."
        
        results = self.verification_results
        
        report_lines = [
            "LEAN VERIFICATION REPORT",
            "=" * 50,
            f"Timestamp: {results['timestamp']}",
            f"Duration: {results['duration_seconds']:.2f} seconds",
            "",
            f"PROJECT BUILD: {'✓ SUCCESS' if results['project_build']['success'] else '✗ FAILED'}",
            "",
            "FILE VERIFICATION SUMMARY:",
            f"  Total files: {results['files']['total']}",
            f"  Successful: {results['files']['successful']}",
            f"  Failed: {results['files']['failed']}",
            f"  Success rate: {results['files']['successful'] / results['files']['total'] * 100:.1f}%",
            ""
        ]
        
        # Details for failed files
        failed_files = [r for r in results["file_results"] if not r["success"]]
        if failed_files:
            report_lines.append("FAILED FILES:")
            for result in failed_files:
                report_lines.append(f"  ✗ {result['file']}")
                if "error" in result:
                    report_lines.append(f"    Error: {result['error']}")
                elif result.get("stderr"):
                    # Show first few lines of stderr
                    stderr_lines = result["stderr"].split('\n')[:3]
                    for line in stderr_lines:
                        if line.strip():
                            report_lines.append(f"    {line.strip()}")
            report_lines.append("")
        
        # Details for successful files
        successful_files = [r for r in results["file_results"] if r["success"]]
        if successful_files:
            report_lines.append("SUCCESSFUL FILES:")
            for result in successful_files:
                report_lines.append(f"  ✓ {result['file']}")
        
        report_text = '\n'.join(report_lines)
        
        if output_file:
            with open(output_file, 'w') as f:
                f.write(report_text)
            print(f"Report written to {output_file}")
        
        return report_text

def main():
    """Main entry point for command line usage."""
    if len(sys.argv) < 2:
        print("Usage: python lean_verifier.py <lean_project_root>")
        sys.exit(1)
    
    project_root = sys.argv[1]
    
    if not Path(project_root).exists():
        print(f"Error: Project root '{project_root}' does not exist")
        sys.exit(1)
    
    verifier = LeanVerifier(project_root)
    
    # Run verification
    print("Running Lean verification...")
    results = verifier.verify_all_files()
    
    # Generate and display report
    report = verifier.generate_report("lean_verification_report.txt")
    print("\n" + report)
    
    # Save detailed results as JSON
    with open("lean_verification_results.json", "w") as f:
        json.dump(results, f, indent=2)
    
    # Exit with error code if verification failed
    if not results["summary"]["all_files_verified"]:
        sys.exit(1)

if __name__ == "__main__":
    main()