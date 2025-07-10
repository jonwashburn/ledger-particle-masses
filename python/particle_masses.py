"""
Recognition Science: Particle Mass Calculator
============================================

All masses derived from E_r = E_coh × φ^r with NO free parameters.
"""

import math
from dataclasses import dataclass
from typing import Dict, List, Optional

from foundation import J, PHI
from constants import E_COH, PARTICLE_RUNGS, PARTICLE_SECTORS, EXPERIMENTAL_MASSES
from ledger import φ_ladder_mass


@dataclass
class ParticleMass:
    """Complete mass data for a particle."""
    name: str
    rung: int
    raw_mass_mev: float
    physical_mass_mev: float
    pdg_mass_mev: Optional[float] = None
    error_percent: Optional[float] = None


def calculate_masses():
    """Calculate all particle masses."""
    results = []
    
    for particle, rung in PARTICLE_RUNGS.items():
        raw_mass = φ_ladder_mass(rung)
        # Temporary: no dressing for initial test
        physical_mass = raw_mass
        
        pdg_mass = EXPERIMENTAL_MASSES.get(particle)
        error = None
        if pdg_mass:
            error = abs(physical_mass - pdg_mass) / pdg_mass * 100
        
        results.append(ParticleMass(
            name=particle, 
            rung=rung,
            raw_mass_mev=raw_mass,
            physical_mass_mev=physical_mass,
            pdg_mass_mev=pdg_mass,
            error_percent=error
        ))
    
    return results


if __name__ == "__main__":
    print("Recognition Science - Pure φ-ladder Test")
    print("=" * 60)
    print(f"E_r = E_coh × φ^r where E_coh = {E_COH} eV")
    print(f"Golden ratio φ = {PHI:.15f}")
    print()
    
    results = calculate_masses()
    
    # Show a few examples
    print("Sample masses (NO dressing applied):")
    for name in ['electron', 'muon', 'up', 'W']:
        for r in results:
            if r.name == name:
                print(f"{r.name}: rung {r.rung}, raw {r.raw_mass_mev:.6f} MeV")
                if r.pdg_mass_mev:
                    print(f"  PDG: {r.pdg_mass_mev:.3f} MeV, needs dressing factor: {r.pdg_mass_mev/r.raw_mass_mev:.1f}")
