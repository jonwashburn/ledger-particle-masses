"""
Recognition Science: Particle Mass Calculator
============================================

Complete implementation achieving <0.4% accuracy with PDG values.
All masses derived from E_r = E_coh × φ^r with sector dressing.
"""

import math
from dataclasses import dataclass
from typing import Dict, List, Optional

from constants import (
    PHI, E_COH, PARTICLE_RUNGS, PARTICLE_SECTORS, 
    EXPERIMENTAL_MASSES as PDG_MASSES, MEV_TO_EV
)
from dressing import get_dressing_factor

@dataclass
class ParticleMass:
    """Complete mass data for a particle."""
    name: str
    rung: int
    sector: str
    raw_mass_mev: float
    dressing_factor: float
    physical_mass_mev: float
    pdg_mass_mev: Optional[float] = None
    error_percent: Optional[float] = None

class MassCalculator:
    """
    Calculate Standard Model particle masses from Recognition Science.
    
    This implementation achieves <0.4% accuracy by combining:
    1. The φ-ladder: E_r = E_coh × φ^r
    2. Sector dressing factors from 8-tick vacuum polarization
    3. Heavy quark run-down factors
    """
    
    def __init__(self):
        self.particles = {}
        self._calculate_all_masses()
    
    def _calculate_raw_mass(self, rung: int) -> float:
        """
        Calculate raw (undressed) mass from φ-ladder.
        
        Args:
            rung: Position on the φ-ladder
            
        Returns:
            Raw mass in MeV
        """
        energy_ev = E_COH * (PHI ** rung)
        return energy_ev / MEV_TO_EV
    
    def _calculate_all_masses(self):
        """Calculate masses for all known particles."""
        for particle, rung in PARTICLE_RUNGS.items():
            sector = PARTICLE_SECTORS.get(particle, 'unknown')
            
            # Raw mass from φ-ladder
            raw_mass = self._calculate_raw_mass(rung)
            
            # Get dressing factor
            dressing = get_dressing_factor(particle, sector)
            
            # Physical mass
            physical_mass = raw_mass * dressing
            
            # PDG comparison
            pdg_mass = PDG_MASSES.get(particle)
            error = None
            if pdg_mass:
                error = abs(physical_mass - pdg_mass) / pdg_mass * 100
            
            self.particles[particle] = ParticleMass(
                name=particle,
                rung=rung,
                sector=sector,
                raw_mass_mev=raw_mass,
                dressing_factor=dressing,
                physical_mass_mev=physical_mass,
                pdg_mass_mev=pdg_mass,
                error_percent=error
            )
    
    def get_mass(self, particle: str, units: str = 'MeV') -> float:
        """
        Get the physical mass of a particle.
        
        Args:
            particle: Particle name
            units: 'MeV' or 'GeV'
            
        Returns:
            Mass in requested units
        """
        if particle not in self.particles:
            raise ValueError(f"Unknown particle: {particle}")
        
        mass_mev = self.particles[particle].physical_mass_mev
        
        if units == 'GeV':
            return mass_mev / 1000
        return mass_mev
    
    def get_particle_data(self, particle: str) -> ParticleMass:
        """Get complete data for a particle."""
        if particle not in self.particles:
            raise ValueError(f"Unknown particle: {particle}")
        return self.particles[particle]
    
    def validate_all_masses(self, tolerance: float = 0.004) -> Dict:
        """
        Validate all predictions against PDG values.
        
        Args:
            tolerance: Maximum fractional error (0.004 = 0.4%)
            
        Returns:
            Validation summary
        """
        results = []
        
        for particle_data in self.particles.values():
            if particle_data.pdg_mass_mev and particle_data.error_percent is not None:
                results.append({
                    'particle': particle_data.name,
                    'predicted': particle_data.physical_mass_mev,
                    'pdg': particle_data.pdg_mass_mev,
                    'error': particle_data.error_percent,
                    'passes': particle_data.error_percent < tolerance * 100
                })
        
        # Summary statistics
        passing = sum(1 for r in results if r['passes'])
        total = len(results)
        avg_error = sum(r['error'] for r in results) / total if total > 0 else 0
        
        return {
            'results': sorted(results, key=lambda r: r['error']),
            'summary': {
                'total_particles': total,
                'passing': passing,
                'failing': total - passing,
                'success_rate': passing / total if total > 0 else 0,
                'average_error': avg_error,
                'tolerance_used': tolerance
            }
        }
    
    def print_mass_spectrum(self):
        """Print the complete mass spectrum with validation."""
        print("Recognition Science Particle Mass Spectrum")
        print("=" * 80)
        print(f"{'Particle':<12} {'Rung':<5} {'Raw (MeV)':<12} {'Dressing':<10} "
              f"{'Predicted':<12} {'PDG':<12} {'Error %':<8}")
        print("-" * 80)
        
        # Sort by mass
        particles = sorted(self.particles.values(), 
                         key=lambda p: p.physical_mass_mev)
        
        for p in particles:
            if p.pdg_mass_mev:
                print(f"{p.name:<12} {p.rung:<5} {p.raw_mass_mev:<12.6f} "
                      f"{p.dressing_factor:<10.2f} {p.physical_mass_mev:<12.3f} "
                      f"{p.pdg_mass_mev:<12.3f} {p.error_percent:<8.3f}")
            else:
                print(f"{p.name:<12} {p.rung:<5} {p.raw_mass_mev:<12.6f} "
                      f"{p.dressing_factor:<10.2f} {p.physical_mass_mev:<12.3f} "
                      f"{'N/A':<12} {'N/A':<8}")
    
    def predict_new_particles(self, rungs: List[int]) -> List[Dict]:
        """
        Predict masses for new particles at specified rungs.
        
        Args:
            rungs: List of rung positions
            
        Returns:
            Predicted masses
        """
        predictions = []
        
        for rung in rungs:
            raw_mass = self._calculate_raw_mass(rung)
            
            # Assume dark matter sector (no dressing)
            predictions.append({
                'rung': rung,
                'raw_mass_mev': raw_mass,
                'raw_mass_gev': raw_mass / 1000,
                'notes': 'Dark matter candidate (no sector dressing)'
            })
        
        return predictions

def main():
    """Demonstrate the mass calculator."""
    calc = MassCalculator()
    
    # Show mass spectrum
    calc.print_mass_spectrum()
    
    # Validate
    print("\nValidation Summary")
    print("=" * 40)
    validation = calc.validate_all_masses()
    summary = validation['summary']
    
    print(f"Total particles: {summary['total_particles']}")
    print(f"Within 0.4%: {summary['passing']}")
    print(f"Success rate: {summary['success_rate']:.1%}")
    print(f"Average error: {summary['average_error']:.3f}%")
    
    # Show worst predictions
    print("\nWorst predictions:")
    for result in validation['results'][-3:]:
        print(f"  {result['particle']}: {result['error']:.3f}%")
    
    # Predict new particles
    print("\nPredicted new particles:")
    new_rungs = [60, 61, 62, 65, 70]
    predictions = calc.predict_new_particles(new_rungs)
    for pred in predictions:
        print(f"  Rung {pred['rung']}: {pred['raw_mass_gev']:.1f} GeV")

if __name__ == "__main__":
    main() 