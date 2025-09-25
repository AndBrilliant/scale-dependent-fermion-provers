"""
Renormalization Group flow equations for fermion masses and gauge couplings.

This module implements the mathematical framework for RG evolution of 
physical parameters in quantum field theories.
"""

import numpy as np
from typing import Callable, Dict, Any
from scipy.integrate import solve_ivp

class RGFlow:
    """Represents RG flow with beta functions."""
    
    def __init__(self, beta_functions: Dict[str, Callable]):
        """
        Initialize RG flow with beta functions.
        
        Args:
            beta_functions: Dictionary mapping parameter names to beta functions
        """
        self.beta_functions = beta_functions
    
    def flow_equations(self, t: float, y: np.ndarray) -> np.ndarray:
        """
        RG flow equations dy/dt = β(y).
        
        Args:
            t: RG scale parameter (log of energy scale)
            y: Array of coupling constants
            
        Returns:
            Array of beta function values
        """
        # Map array elements to parameter dictionary
        params = dict(zip(self.beta_functions.keys(), y))
        
        # Evaluate beta functions
        dydt = np.array([
            beta_func(**params) for beta_func in self.beta_functions.values()
        ])
        
        return dydt
    
    def solve(self, initial_conditions: Dict[str, float], 
              t_span: tuple, num_points: int = 100) -> Dict[str, Any]:
        """
        Solve RG flow equations.
        
        Args:
            initial_conditions: Initial values for parameters
            t_span: (t_initial, t_final) for integration
            num_points: Number of solution points
            
        Returns:
            Dictionary with solution arrays
        """
        y0 = np.array(list(initial_conditions.values()))
        t_eval = np.linspace(t_span[0], t_span[1], num_points)
        
        solution = solve_ivp(
            self.flow_equations, t_span, y0, t_eval=t_eval, 
            method='RK45', rtol=1e-8
        )
        
        result = {
            't': solution.t,
            'success': solution.success
        }
        
        # Map solution back to parameter names
        for i, param_name in enumerate(self.beta_functions.keys()):
            result[param_name] = solution.y[i]
            
        return result

def fermion_mass_beta(g: float, m: float, **kwargs) -> float:
    """
    Beta function for fermion mass.
    
    Args:
        g: Gauge coupling constant
        m: Fermion mass
        
    Returns:
        β_m = γ_m * m where γ_m is anomalous dimension
    """
    # Simplified one-loop anomalous dimension
    gamma_m = (3 * g**2) / (16 * np.pi**2)
    return gamma_m * m

def gauge_coupling_beta(g: float, **kwargs) -> float:
    """
    Beta function for gauge coupling (one-loop QED).
    
    Args:
        g: Gauge coupling constant
        
    Returns:
        β_g for QED with N_f fermion flavors
    """
    N_f = 3  # Number of fermion flavors
    return (2 * N_f * g**3) / (3 * 4 * np.pi)**2

def yukawa_coupling_beta(y: float, g: float, **kwargs) -> float:
    """
    Beta function for Yukawa coupling.
    
    Args:
        y: Yukawa coupling
        g: Gauge coupling
        
    Returns:
        β_y for Yukawa coupling
    """
    # Simplified beta function
    return (3 * y**3 - 9 * g**2 * y) / (16 * np.pi**2)

# Example usage
if __name__ == "__main__":
    # Define beta functions
    beta_funcs = {
        'g': gauge_coupling_beta,
        'm': fermion_mass_beta,
        'y': yukawa_coupling_beta
    }
    
    rg_flow = RGFlow(beta_funcs)
    
    # Initial conditions at some energy scale
    initial = {'g': 0.3, 'm': 0.1, 'y': 0.5}
    
    # Solve RG equations from log(E_initial) to log(E_final)
    solution = rg_flow.solve(initial, (0, 10), 200)
    
    if solution['success']:
        print("RG flow solved successfully")
        print(f"Final values: g={solution['g'][-1]:.4f}, "
              f"m={solution['m'][-1]:.4f}, y={solution['y'][-1]:.4f}")
    else:
        print("RG flow solution failed")