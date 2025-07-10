"""
Recognition Science Foundation Layer
====================================

This module implements the universal cost functional J(x) = ½(x + 1/x) and
the eight axioms from which all physical constants derive.

Zero free parameters - everything emerges from the meta-principle:
"Nothing cannot recognize itself"
"""

import math
import numpy as np
from typing import Tuple, Optional, List
from dataclasses import dataclass


# =============================================================================
# The Universal Cost Functional
# =============================================================================

def J(x: float) -> float:
    """
    The universal cost functional J(x) = ½(x + 1/x).
    
    This is THE fundamental equation of Recognition Science.
    It measures the ledger cost of any recognition hop.
    
    Properties:
    - J(x) = J(1/x) (dual-recognition symmetry)
    - Minimum at x = 1 with J(1) = 1
    - For x > 1, strictly increasing
    
    Args:
        x: The recognition ratio (must be > 0)
        
    Returns:
        The cost value
    """
    if x <= 0:
        raise ValueError("x must be positive for cost functional")
    return 0.5 * (x + 1/x)


def dJ_dx(x: float) -> float:
    """
    First derivative of cost functional: J'(x) = ½(1 - 1/x²).
    
    Critical points: J'(x) = 0 when x = ±1
    For x > 0, only x = 1 is the critical point.
    """
    if x <= 0:
        raise ValueError("x must be positive")
    return 0.5 * (1 - 1/(x**2))


def d2J_dx2(x: float) -> float:
    """
    Second derivative of cost functional: J''(x) = 1/x³.
    
    Always positive for x > 0, confirming J is strictly convex.
    """
    if x <= 0:
        raise ValueError("x must be positive")
    return 1 / (x**3)


def find_cost_minimum(x_min: float = 0.1, x_max: float = 10.0, tol: float = 1e-12) -> float:
    """
    Find the minimum of the cost functional numerically.
    
    Result should be x = 1 with J(1) = 1.
    """
    # Use golden section search for robustness
    phi = (1 + math.sqrt(5)) / 2
    resphi = 2 - phi
    
    # Initial bounds
    a, b = x_min, x_max
    tau = resphi * (b - a)
    
    x1 = a + tau
    x2 = b - tau
    f1 = J(x1)
    f2 = J(x2)
    
    while abs(b - a) > tol:
        if f1 < f2:
            b = x2
            x2 = x1
            f2 = f1
            tau = resphi * (b - a)
            x1 = a + tau
            f1 = J(x1)
        else:
            a = x1
            x1 = x2
            f1 = f2
            tau = resphi * (b - a)
            x2 = b - tau
            f2 = J(x2)
    
    return (a + b) / 2


# =============================================================================
# The Eight Axioms
# =============================================================================

@dataclass
class Axiom:
    """Represents one of the eight Recognition Science axioms."""
    number: int
    name: str
    statement: str
    mathematical_form: str


# The Eight Recognition Axioms (from manuscript)
AXIOMS = [
    Axiom(
        1, 
        "Observation Alters Ledger",
        "Any act of recognition transfers a finite, non-negative cost ΔJ from potential to realized ledger.",
        "ΔJ = J_real - J_pot ≥ 0"
    ),
    Axiom(
        2,
        "Dual-Recognition Symmetry", 
        "Every ledger change has a conjugate that restores balance.",
        "J(x) = J(1/x)"
    ),
    Axiom(
        3,
        "Cost-Functional Minimization",
        "Physical paths minimize integrated cost S = ∫J(x(t))dt.",
        "δS = 0 ⟹ ẍ = x - 1/x³"
    ),
    Axiom(
        4,
        "Information Is Physical",
        "Every bit costs E_coh = 0.090 eV in ledger currency.",
        "ΔJ = E_coh × ΔI"
    ),
    Axiom(
        5,
        "Conservation of Recognition Flow",
        "Cost density obeys continuity equation.",
        "∂ρ/∂t + ∇·J = 0"
    ),
    Axiom(
        6,
        "Self-Similarity Across Scale",
        "Configurations repeat at scales separated by φⁿ.",
        "r_{n+1} = φ × r_n"
    ),
    Axiom(
        7,
        "Zero Free Parameters",
        "All quantities derive from axioms or count recognition events.",
        "No adjustable constants"
    ),
    Axiom(
        8,
        "Finite Ledger Cycle Time",
        "Recognition flows settle to zero after exactly 8 ticks.",
        "J(t + 8τ₀) = 0"
    )
]


# =============================================================================
# The Golden Ratio - Forced by Cost Minimization
# =============================================================================

# The golden ratio φ = (1 + √5) / 2
PHI = (1 + math.sqrt(5)) / 2

def verify_golden_ratio_minimizes_iterative_cost() -> bool:
    """
    Verify that φ is the unique scaling factor that minimizes 
    accumulated cost over repeated scalings.
    
    Key insight: For any other ratio λ ≠ φ, iterative scaling
    produces residual cost that violates zero-debt requirement.
    """
    # Test various scaling factors
    test_ratios = np.linspace(1.1, 2.0, 100)
    min_cost = float('inf')
    optimal_ratio = None
    
    for ratio in test_ratios:
        # Compute cost over 8 iterations (one audit cycle)
        total_cost = 0
        x = 1.0  # Start at equilibrium
        
        for _ in range(8):
            x *= ratio
            total_cost += J(x)
            x = 1/x  # Dual recognition
            total_cost += J(x)
            x = 1/x  # Return
        
        if total_cost < min_cost:
            min_cost = total_cost
            optimal_ratio = ratio
    
    # Verify it's golden ratio within numerical tolerance
    return abs(optimal_ratio - PHI) < 1e-3


def golden_ratio_equation() -> float:
    """
    Verify φ² = φ + 1.
    
    This is THE key equation that locks in the golden ratio.
    """
    return PHI**2 - PHI - 1  # Should be ~0


def inverse_golden_ratio() -> float:
    """
    Verify 1/φ = φ - 1.
    
    This shows the self-similar property of φ.
    """
    return 1/PHI - (PHI - 1)  # Should be ~0


# =============================================================================
# Euler-Lagrange Equation from Cost Minimization
# =============================================================================

def euler_lagrange_equation(x: float, x_dot: float = 0) -> float:
    """
    The Euler-Lagrange equation from minimizing S = ∫J(x(t))dt.
    
    Result: ẍ = x - 1/x³
    
    This is the fundamental equation of motion in Recognition Science.
    """
    if x <= 0:
        raise ValueError("x must be positive")
    return x - 1/(x**3)


def solve_euler_lagrange(x0: float = 1.0, v0: float = 0.1, 
                        t_max: float = 10.0, dt: float = 0.01) -> Tuple[np.ndarray, np.ndarray]:
    """
    Numerically solve the Euler-Lagrange equation.
    
    Args:
        x0: Initial position
        v0: Initial velocity  
        t_max: Maximum time
        dt: Time step
        
    Returns:
        times, positions arrays
    """
    times = np.arange(0, t_max, dt)
    n = len(times)
    x = np.zeros(n)
    v = np.zeros(n)
    
    # Initial conditions
    x[0] = x0
    v[0] = v0
    
    # Velocity Verlet integration
    for i in range(n-1):
        a = euler_lagrange_equation(x[i])
        x[i+1] = x[i] + v[i]*dt + 0.5*a*dt**2
        a_new = euler_lagrange_equation(x[i+1])
        v[i+1] = v[i] + 0.5*(a + a_new)*dt
        
    return times, x


# =============================================================================
# Ledger Balance Functions
# =============================================================================

@dataclass
class LedgerState:
    """
    Represents a ledger state with flow and stock columns.
    """
    flow: np.ndarray  # Flow column values
    stock: np.ndarray  # Stock column values
    tick: int = 0  # Current tick in 8-tick cycle
    
    @property
    def total_cost(self) -> float:
        """Total cost across all cells."""
        return np.sum(self.flow) + np.sum(self.stock)
    
    @property
    def is_balanced(self) -> bool:
        """Check if ledger is balanced (equal flow and stock)."""
        return np.allclose(np.sum(self.flow), np.sum(self.stock))
    
    def dual_transform(self) -> 'LedgerState':
        """Apply dual transformation (swap flow and stock)."""
        return LedgerState(
            flow=self.stock.copy(),
            stock=self.flow.copy(),
            tick=self.tick
        )


def eight_tick_evolution(state: LedgerState) -> List[LedgerState]:
    """
    Simulate one complete 8-tick audit cycle.
    
    Returns list of states at each tick.
    """
    states = [state]
    current = state
    
    for tick in range(1, 9):
        # Simplified evolution - actual implementation would include
        # voxel dynamics, face pressures, etc.
        new_state = LedgerState(
            flow=current.flow * PHI**(1/8),
            stock=current.stock * PHI**(-1/8),
            tick=tick % 8
        )
        states.append(new_state)
        current = new_state
    
    return states


# =============================================================================
# Verification Functions
# =============================================================================

def verify_foundation_principles() -> dict:
    """
    Verify all foundation principles are satisfied.
    
    Returns dict with verification results.
    """
    results = {}
    
    # 1. Cost functional minimum
    x_min = find_cost_minimum()
    results['cost_minimum_at_unity'] = abs(x_min - 1.0) < 1e-10
    results['cost_at_minimum'] = abs(J(x_min) - 1.0) < 1e-10
    
    # 2. Dual symmetry
    test_x = 2.5
    results['dual_symmetry'] = abs(J(test_x) - J(1/test_x)) < 1e-10
    
    # 3. Golden ratio properties
    results['golden_ratio_equation'] = abs(golden_ratio_equation()) < 1e-10
    results['golden_inverse'] = abs(inverse_golden_ratio()) < 1e-10
    results['golden_minimizes_cost'] = verify_golden_ratio_minimizes_iterative_cost()
    
    # 4. Cost functional convexity
    x1, x2 = 0.5, 2.0
    lambda_param = 0.3
    x_mid = lambda_param * x1 + (1 - lambda_param) * x2
    results['convexity'] = J(x_mid) <= lambda_param * J(x1) + (1 - lambda_param) * J(x2)
    
    return results


if __name__ == "__main__":
    print("Recognition Science Foundation Layer")
    print("=" * 50)
    
    # Verify foundation principles
    print("\nVerifying foundation principles...")
    results = verify_foundation_principles()
    
    for principle, verified in results.items():
        status = "✓" if verified else "✗"
        print(f"{status} {principle}: {verified}")
    
    # Display key constants
    print(f"\nGolden ratio φ = {PHI:.15f}")
    print(f"φ² - φ - 1 = {golden_ratio_equation():.2e}")
    print(f"J(φ) = {J(PHI):.15f}")
    
    # Show axioms
    print("\nThe Eight Recognition Axioms:")
    for axiom in AXIOMS:
        print(f"\nA{axiom.number}: {axiom.name}")
        print(f"   {axiom.statement}") 