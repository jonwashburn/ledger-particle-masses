"""
Recognition Science: Particle Mass Calculator
============================================

Comprehensive calculator for particle masses using the Recognition Science framework.
Implements the φ-ladder energy cascade with sector dressing factors.

Based on the Recognition Science theory by Jonathan Washburn
Formula: E_r = E_coh × φ^r with sector-specific dressing factors
"""

import math
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from recognition_constants import *

@dataclass
class ParticleData:
    """Complete data for a particle in the Recognition Science framework."""
    name: str
    rung: int
    sector: str
    raw_mass_mev: float
    dressing_factor: float
    dressed_mass_mev: float
    experimental_mass_mev: Optional[float] = None
    error_percent: Optional[float] = None
    
    def __post_init__(self):
        """Calculate derived quantities after initialization."""
        if self.experimental_mass_mev is not None:
            self.error_percent = abs(self.dressed_mass_mev - self.experimental_mass_mev) / self.experimental_mass_mev * 100

class ParticleMassCalculator:
    """
    Main calculator class for Recognition Science particle masses.
    """
    
    def __init__(self):
        """Initialize the calculator with Recognition Science constants."""
        self.phi = PHI
        self.e_coh = E_COH
        self.particles = {}
        self._load_particle_data()
    
    def _load_particle_data(self):
        """Load all particle data into memory."""
        for particle_name, rung in PARTICLE_RUNGS.items():
            sector = PARTICLE_SECTORS.get(particle_name, 'unknown')
            raw_mass = mass_at_rung_mev(rung)
            dressing_factor = get_sector_dressing_factor(particle_name)
            dressed_mass = raw_mass * dressing_factor
            experimental_mass = EXPERIMENTAL_MASSES.get(particle_name)
            
            self.particles[particle_name] = ParticleData(
                name=particle_name,
                rung=rung,
                sector=sector,
                raw_mass_mev=raw_mass,
                dressing_factor=dressing_factor,
                dressed_mass_mev=dressed_mass,
                experimental_mass_mev=experimental_mass
            )
    
    def get_particle(self, name: str) -> ParticleData:
        """
        Get complete particle data.
        
        Args:
            name: Particle name
            
        Returns:
            ParticleData object with all information
        """
        if name not in self.particles:
            raise ValueError(f"Unknown particle: {name}")
        return self.particles[name]
    
    def calculate_mass(self, particle: str, units: str = 'MeV') -> float:
        """
        Calculate the dressed (physical) mass of a particle.
        
        Args:
            particle: Particle name
            units: Units for output ('MeV', 'GeV', 'kg', 'eV')
            
        Returns:
            Particle mass in specified units
        """
        particle_data = self.get_particle(particle)
        mass_mev = particle_data.dressed_mass_mev
        
        if units == 'MeV':
            return mass_mev
        elif units == 'GeV':
            return mass_mev / 1000
        elif units == 'eV':
            return mass_mev * 1e6
        elif units == 'kg':
            return mass_mev * MEV_TO_KG
        else:
            raise ValueError(f"Unknown units: {units}")
    
    def calculate_energy_at_rung(self, rung: int, units: str = 'eV') -> float:
        """
        Calculate energy at a specific rung.
        
        Args:
            rung: Rung number
            units: Units for output ('eV', 'MeV', 'GeV', 'J')
            
        Returns:
            Energy in specified units
        """
        energy_ev = energy_at_rung(rung)
        
        if units == 'eV':
            return energy_ev
        elif units == 'MeV':
            return energy_ev / 1e6
        elif units == 'GeV':
            return energy_ev / 1e9
        elif units == 'J':
            return energy_ev * EV_TO_JOULE
        else:
            raise ValueError(f"Unknown units: {units}")
    
    def get_mass_spectrum(self, sort_by: str = 'mass') -> List[ParticleData]:
        """
        Get the complete mass spectrum.
        
        Args:
            sort_by: How to sort ('mass', 'rung', 'name', 'error')
            
        Returns:
            List of ParticleData objects, sorted as requested
        """
        particles = list(self.particles.values())
        
        if sort_by == 'mass':
            particles.sort(key=lambda p: p.dressed_mass_mev)
        elif sort_by == 'rung':
            particles.sort(key=lambda p: p.rung)
        elif sort_by == 'name':
            particles.sort(key=lambda p: p.name)
        elif sort_by == 'error':
            # Sort by error, putting None values last
            particles.sort(key=lambda p: p.error_percent if p.error_percent is not None else float('inf'))
        
        return particles
    
    def validate_prediction(self, particle: str, tolerance: float = 0.05) -> Dict:
        """
        Validate a specific particle prediction.
        
        Args:
            particle: Particle name
            tolerance: Acceptable fractional error
            
        Returns:
            Validation results dictionary
        """
        particle_data = self.get_particle(particle)
        
        if particle_data.experimental_mass_mev is None:
            return {
                'particle': particle,
                'status': 'no_experimental_data',
                'predicted_mev': particle_data.dressed_mass_mev,
                'rung': particle_data.rung,
                'sector': particle_data.sector
            }
        
        error = abs(particle_data.dressed_mass_mev - particle_data.experimental_mass_mev) / particle_data.experimental_mass_mev
        
        return {
            'particle': particle,
            'predicted_mev': particle_data.dressed_mass_mev,
            'experimental_mev': particle_data.experimental_mass_mev,
            'fractional_error': error,
            'percent_error': error * 100,
            'within_tolerance': error < tolerance,
            'rung': particle_data.rung,
            'sector': particle_data.sector,
            'dressing_factor': particle_data.dressing_factor,
            'status': 'validated'
        }
    
    def validate_all_predictions(self, tolerance: float = 0.05) -> Dict:
        """
        Validate all predictions with experimental data.
        
        Args:
            tolerance: Acceptable fractional error
            
        Returns:
            Complete validation results
        """
        results = {}
        validated_particles = []
        accurate_predictions = []
        
        for particle_name in self.particles:
            result = self.validate_prediction(particle_name, tolerance)
            results[particle_name] = result
            
            if result['status'] == 'validated':
                validated_particles.append(particle_name)
                if result['within_tolerance']:
                    accurate_predictions.append(particle_name)
        
        # Calculate statistics
        total_validated = len(validated_particles)
        total_accurate = len(accurate_predictions)
        
        if total_validated > 0:
            accuracy_rate = total_accurate / total_validated
            average_error = sum(results[p]['percent_error'] for p in validated_particles) / total_validated
        else:
            accuracy_rate = 0
            average_error = 0
        
        return {
            'individual_results': results,
            'summary': {
                'total_particles': len(self.particles),
                'validated_particles': total_validated,
                'accurate_predictions': total_accurate,
                'accuracy_rate': accuracy_rate,
                'average_error_percent': average_error,
                'tolerance_used': tolerance
            }
        }
    
    def predict_new_particles(self, min_rung: int = 55, max_rung: int = 75) -> List[Dict]:
        """
        Predict masses for new particles at unoccupied rungs.
        
        Args:
            min_rung: Minimum rung to consider
            max_rung: Maximum rung to consider
            
        Returns:
            List of predicted new particles
        """
        occupied_rungs = {p.rung for p in self.particles.values()}
        predictions = []
        
        for rung in range(min_rung, max_rung + 1):
            if rung not in occupied_rungs:
                energy_ev = energy_at_rung(rung)
                mass_mev = energy_ev / 1e6
                
                predictions.append({
                    'rung': rung,
                    'energy_ev': energy_ev,
                    'mass_mev': mass_mev,
                    'mass_gev': mass_mev / 1000,
                    'suggested_name': f'new_particle_{rung}'
                })
        
        return predictions
    
    def calculate_mass_ratios(self) -> Dict[str, float]:
        """
        Calculate important mass ratios.
        
        Returns:
            Dictionary of mass ratios
        """
        ratios = {}
        
        # Lepton mass ratios
        if all(p in self.particles for p in ['electron', 'muon', 'tau']):
            ratios['muon_electron'] = self.particles['muon'].dressed_mass_mev / self.particles['electron'].dressed_mass_mev
            ratios['tau_electron'] = self.particles['tau'].dressed_mass_mev / self.particles['electron'].dressed_mass_mev
            ratios['tau_muon'] = self.particles['tau'].dressed_mass_mev / self.particles['muon'].dressed_mass_mev
        
        # Quark mass ratios
        if all(p in self.particles for p in ['up', 'down']):
            ratios['down_up'] = self.particles['down'].dressed_mass_mev / self.particles['up'].dressed_mass_mev
        
        # Boson mass ratios
        if all(p in self.particles for p in ['W_boson', 'Z_boson']):
            ratios['Z_W'] = self.particles['Z_boson'].dressed_mass_mev / self.particles['W_boson'].dressed_mass_mev
        
        if all(p in self.particles for p in ['higgs', 'W_boson']):
            ratios['higgs_W'] = self.particles['higgs'].dressed_mass_mev / self.particles['W_boson'].dressed_mass_mev
        
        return ratios
    
    def print_mass_spectrum(self, sort_by: str = 'mass', show_errors: bool = True):
        """
        Print the complete mass spectrum in a formatted table.
        
        Args:
            sort_by: How to sort the output
            show_errors: Whether to show prediction errors
        """
        particles = self.get_mass_spectrum(sort_by)
        
        print("Recognition Science Particle Mass Spectrum")
        print("=" * 80)
        
        # Header
        if show_errors:
            print(f"{'Particle':<15} {'Rung':<5} {'Sector':<12} {'Predicted':<12} {'Experimental':<12} {'Error %':<8}")
            print("-" * 80)
        else:
            print(f"{'Particle':<15} {'Rung':<5} {'Sector':<12} {'Predicted':<12} {'Dressing':<10}")
            print("-" * 70)
        
        # Data rows
        for particle in particles:
            if show_errors and particle.experimental_mass_mev is not None:
                error_str = f"{particle.error_percent:.1f}%" if particle.error_percent is not None else "N/A"
                print(f"{particle.name:<15} {particle.rung:<5} {particle.sector:<12} "
                      f"{particle.dressed_mass_mev:<12.3f} {particle.experimental_mass_mev:<12.3f} {error_str:<8}")
            else:
                print(f"{particle.name:<15} {particle.rung:<5} {particle.sector:<12} "
                      f"{particle.dressed_mass_mev:<12.3f} {particle.dressing_factor:<10.2f}")
        
        print()
    
    def print_validation_summary(self):
        """Print a summary of validation results."""
        validation = self.validate_all_predictions()
        summary = validation['summary']
        
        print("Validation Summary")
        print("=" * 40)
        print(f"Total particles: {summary['total_particles']}")
        print(f"Validated particles: {summary['validated_particles']}")
        print(f"Accurate predictions: {summary['accurate_predictions']}")
        print(f"Accuracy rate: {summary['accuracy_rate']:.1%}")
        print(f"Average error: {summary['average_error_percent']:.1f}%")
        print(f"Tolerance used: {summary['tolerance_used']:.1%}")
        
        # Show best and worst predictions
        results = validation['individual_results']
        validated_results = {k: v for k, v in results.items() if v['status'] == 'validated'}
        
        if validated_results:
            best = min(validated_results.items(), key=lambda x: x[1]['percent_error'])
            worst = max(validated_results.items(), key=lambda x: x[1]['percent_error'])
            
            print()
            print(f"Best prediction: {best[0]} ({best[1]['percent_error']:.1f}% error)")
            print(f"Worst prediction: {worst[0]} ({worst[1]['percent_error']:.1f}% error)")

def main():
    """Demonstration of the particle mass calculator."""
    calc = ParticleMassCalculator()
    
    # Print constants
    print_constants()
    print()
    
    # Show mass spectrum
    calc.print_mass_spectrum()
    
    # Show validation summary
    calc.print_validation_summary()
    
    # Show mass ratios
    print("\nImportant Mass Ratios")
    print("=" * 30)
    ratios = calc.calculate_mass_ratios()
    for ratio_name, value in ratios.items():
        print(f"{ratio_name}: {value:.1f}")
    
    # Show predictions for new particles
    print("\nPredicted New Particles")
    print("=" * 30)
    new_particles = calc.predict_new_particles(59, 65)
    for particle in new_particles:
        print(f"Rung {particle['rung']}: {particle['mass_gev']:.1f} GeV")

if __name__ == "__main__":
    main() 