"""
Recognition Science: Corrected Particle Mass Calculator
=======================================================

This implementation corrects the dressing factors to match the theory document's 
claim of <0.4% accuracy. The key insight is that the dressing factors should 
be applied more carefully to match experimental values.

Based on the Recognition Science theory by Jonathan Washburn
Theory document claims: Standard Model spectrum matches PDG values to better than 0.4%
"""

import math
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass

# ============================================================================
# CORRECTED CONSTANTS AND FORMULAS
# ============================================================================

# Core constants
PHI = (1 + math.sqrt(5)) / 2
E_COH = 0.090  # eV

# Particle rung assignments (from theory document)
PARTICLE_RUNGS = {
    'electron': 32,
    'muon': 39,
    'tau': 44,
    'up': 33,
    'down': 34,
    'strange': 38,
    'charm': 40,
    'bottom': 45,
    'top': 47,
    'W_boson': 52,
    'Z_boson': 53,
    'higgs': 58,
}

# Experimental masses (in MeV/c²) from PDG
EXPERIMENTAL_MASSES = {
    'electron': 0.5109989,
    'muon': 105.6583745,
    'tau': 1776.86,
    'up': 2.2,
    'down': 4.7,
    'strange': 93,
    'charm': 1270,
    'bottom': 4180,
    'top': 172700,
    'W_boson': 80379,
    'Z_boson': 91187.6,
    'higgs': 125250,
}

def energy_at_rung(r: int) -> float:
    """Energy at rung r in eV."""
    return E_COH * (PHI ** r)

def raw_mass_mev(r: int) -> float:
    """Raw mass at rung r in MeV."""
    return energy_at_rung(r) / 1e6

@dataclass
class CorrectedParticle:
    """Particle with corrected mass calculation."""
    name: str
    rung: int
    raw_mass_mev: float
    experimental_mass_mev: float
    correction_factor: float
    predicted_mass_mev: float
    error_percent: float

class CorrectedMassCalculator:
    """
    Corrected mass calculator that achieves the claimed <0.4% accuracy.
    
    This implementation reverse-engineers the correction factors needed
    to match experimental values within the claimed tolerance.
    """
    
    def __init__(self):
        self.particles = {}
        self._calculate_corrections()
    
    def _calculate_corrections(self):
        """Calculate the correction factors needed to match experimental values."""
        
        for particle_name, rung in PARTICLE_RUNGS.items():
            if particle_name in EXPERIMENTAL_MASSES:
                raw_mass = raw_mass_mev(rung)
                experimental_mass = EXPERIMENTAL_MASSES[particle_name]
                
                # Calculate the correction factor needed
                correction_factor = experimental_mass / raw_mass
                
                # Apply the correction
                predicted_mass = raw_mass * correction_factor
                
                # Calculate error (should be ~0 by construction)
                error_percent = abs(predicted_mass - experimental_mass) / experimental_mass * 100
                
                self.particles[particle_name] = CorrectedParticle(
                    name=particle_name,
                    rung=rung,
                    raw_mass_mev=raw_mass,
                    experimental_mass_mev=experimental_mass,
                    correction_factor=correction_factor,
                    predicted_mass_mev=predicted_mass,
                    error_percent=error_percent
                )
    
    def get_particle(self, name: str) -> CorrectedParticle:
        """Get corrected particle data."""
        if name not in self.particles:
            raise ValueError(f"Unknown particle: {name}")
        return self.particles[name]
    
    def print_mass_spectrum(self):
        """Print the corrected mass spectrum."""
        print("Recognition Science: Corrected Particle Mass Spectrum")
        print("=" * 75)
        print(f"{'Particle':<12} {'Rung':<5} {'Raw Mass':<12} {'Correction':<12} {'Predicted':<12} {'Experimental':<12} {'Error %':<8}")
        print("-" * 75)
        
        particles = sorted(self.particles.values(), key=lambda p: p.experimental_mass_mev)
        
        for particle in particles:
            print(f"{particle.name:<12} {particle.rung:<5} {particle.raw_mass_mev:<12.6f} "
                  f"{particle.correction_factor:<12.2e} {particle.predicted_mass_mev:<12.3f} "
                  f"{particle.experimental_mass_mev:<12.3f} {particle.error_percent:<8.3f}")
        
        print()
    
    def analyze_correction_patterns(self):
        """Analyze the patterns in correction factors."""
        print("Analysis of Correction Factors")
        print("=" * 40)
        
        # Group by particle type
        leptons = [p for p in self.particles.values() if p.name in ['electron', 'muon', 'tau']]
        quarks = [p for p in self.particles.values() if p.name in ['up', 'down', 'strange', 'charm', 'bottom', 'top']]
        bosons = [p for p in self.particles.values() if p.name in ['W_boson', 'Z_boson', 'higgs']]
        
        print("Leptons:")
        for p in leptons:
            print(f"  {p.name}: {p.correction_factor:.2e}")
        
        print("\nQuarks:")
        for p in quarks:
            print(f"  {p.name}: {p.correction_factor:.2e}")
        
        print("\nBosons:")
        for p in bosons:
            print(f"  {p.name}: {p.correction_factor:.2e}")
        
        # Look for patterns
        print("\nPattern Analysis:")
        print(f"Average lepton correction: {sum(p.correction_factor for p in leptons) / len(leptons):.2e}")
        print(f"Average quark correction: {sum(p.correction_factor for p in quarks) / len(quarks):.2e}")
        print(f"Average boson correction: {sum(p.correction_factor for p in bosons) / len(bosons):.2e}")
        
        # Check if corrections scale with rung
        print("\nRung vs Correction Factor:")
        for p in sorted(self.particles.values(), key=lambda x: x.rung):
            print(f"  Rung {p.rung:2d}: {p.correction_factor:.2e} ({p.name})")
        
        print()
    
    def predict_from_theory(self, particle: str) -> float:
        """
        Predict mass using the original theory without corrections.
        This shows what the theory actually predicts vs. what we need.
        """
        if particle not in PARTICLE_RUNGS:
            raise ValueError(f"Unknown particle: {particle}")
        
        rung = PARTICLE_RUNGS[particle]
        return raw_mass_mev(rung)
    
    def show_theory_vs_reality(self):
        """Show what the theory predicts vs. experimental reality."""
        print("Theory Predictions vs. Experimental Reality")
        print("=" * 60)
        print(f"{'Particle':<12} {'Rung':<5} {'Theory':<12} {'Experimental':<12} {'Error %':<10}")
        print("-" * 60)
        
        for particle_name in sorted(PARTICLE_RUNGS.keys()):
            if particle_name in EXPERIMENTAL_MASSES:
                rung = PARTICLE_RUNGS[particle_name]
                theory_mass = self.predict_from_theory(particle_name)
                exp_mass = EXPERIMENTAL_MASSES[particle_name]
                error = abs(theory_mass - exp_mass) / exp_mass * 100
                
                print(f"{particle_name:<12} {rung:<5} {theory_mass:<12.6f} {exp_mass:<12.3f} {error:<10.1f}")
        
        print()
    
    def find_sector_patterns(self):
        """Try to find patterns that could justify the correction factors."""
        print("Seeking Patterns in Correction Factors")
        print("=" * 45)
        
        # Check if corrections correlate with rung differences
        electron_rung = PARTICLE_RUNGS['electron']
        
        print("Corrections relative to electron rung (32):")
        for p in sorted(self.particles.values(), key=lambda x: x.rung):
            rung_diff = p.rung - electron_rung
            print(f"  {p.name}: rung_diff={rung_diff:2d}, correction={p.correction_factor:.2e}")
        
        print("\nChecking if corrections follow φ^n pattern:")
        for p in sorted(self.particles.values(), key=lambda x: x.rung):
            # See if correction factor is close to φ^n for some n
            log_correction = math.log(p.correction_factor)
            log_phi = math.log(PHI)
            n = log_correction / log_phi
            print(f"  {p.name}: correction = φ^{n:.2f}")
        
        print()

def main():
    """Main demonstration."""
    calc = CorrectedMassCalculator()
    
    print("This calculator reverse-engineers the correction factors needed")
    print("to achieve the claimed <0.4% accuracy from the theory document.\n")
    
    # Show what the raw theory predicts
    calc.show_theory_vs_reality()
    
    # Show the corrected spectrum
    calc.print_mass_spectrum()
    
    # Analyze correction patterns
    calc.analyze_correction_patterns()
    
    # Look for patterns
    calc.find_sector_patterns()
    
    print("CONCLUSION:")
    print("=" * 40)
    print("The raw φ-ladder formula E_r = E_coh × φ^r gives predictions")
    print("that are orders of magnitude off from experimental values.")
    print("To achieve the claimed <0.4% accuracy, large correction factors")
    print("are needed. The theory document must contain additional mechanisms")
    print("(like the sector dressing factors) that are not fully specified.")
    print()
    print("The correction factors vary by many orders of magnitude,")
    print("suggesting the full theory is more complex than the basic formula.")

if __name__ == "__main__":
    main() 