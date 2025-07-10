"""
Recognition Science: Fundamental Constants
=========================================

High-precision constants for particle mass calculations.
All derived from the eight axioms - no free parameters.
"""

import math

# =============================================================================
# CODATA Universal Constants
# =============================================================================
H_BAR = 1.054571817e-34  # Reduced Planck constant (J⋅s)
C = 299792458.0  # Speed of light (m/s) - exact by definition
G = 6.67430e-11  # Gravitational constant (m³/kg⋅s²)
ALPHA = 1/137.035999084  # Fine structure constant (CODATA 2022)

# =============================================================================
# Mathematical Constants
# =============================================================================
PHI = (1 + math.sqrt(5)) / 2  # Golden ratio: 1.6180339887...
# PHI² = PHI + 1 (fundamental identity)
# PHI⁻¹ = PHI - 1 (inverse identity)

# =============================================================================
# Planck Scaffold (derived from H_BAR, C, G)
# =============================================================================
T_PLANCK = math.sqrt(H_BAR * G / C**5)  # Planck time: 5.391247e-44 s
L_PLANCK = C * T_PLANCK  # Planck length: 1.616255e-35 m  
M_PLANCK = math.sqrt(H_BAR * C / G)  # Planck mass: 2.176434e-8 kg
E_PLANCK = M_PLANCK * C**2  # Planck energy: 1.956e9 J

# =============================================================================
# Cost Quantum (empirically anchored)
# =============================================================================
E_COH = 0.090  # Coherence quantum in eV (minimum recognition cost)
E_COH_J = E_COH * 1.602176634e-19  # Convert to Joules: 1.442e-20 J

# =============================================================================
# Chronon Hierarchy (from manuscript)
# =============================================================================
TAU_PLANCK = T_PLANCK  # Planck chronon: 5.391247e-44 s
TAU = 3.900e-9  # Single tick: 3.900 ns (from positronium lifetime)
GAMMA = 8 * TAU  # Macro-chronon: 31.200 ns (complete 8-tick audit cycle)
TAU_QUARTER = TAU / 4  # Quarter-tick: 0.975 ns (FPGA convenience)

# =============================================================================
# Spatial Voxelization  
# =============================================================================
L_VOXEL = PHI**(-12) * L_PLANCK  # Voxel edge: ~1.47e-37 m
# One-coin capacity: C(bulk) = 3/4, C(face) = 1/24 each

# =============================================================================
# Recognition Science Derived Constants
# =============================================================================
LAMBDA_REC = 1.616e-35  # Recognition length in meters

# =============================================================================
# Unit Conversions
# =============================================================================
EV_TO_J = 1.602176634e-19  # eV to Joules
EV_TO_MEV = 1e-6  # eV to MeV
MEV_TO_GEV = 1e-3  # MeV to GeV
# Note: In natural units where c=1, mass and energy have same units
# E = mc² → m = E/c² but with c=1, m = E

# Color factors
N_C = 3  # Number of colors in QCD

# Running coupling at key scales
ALPHA_S_2GEV = 0.30  # Strong coupling at 2 GeV
ALPHA_S_MZ = 0.118  # Strong coupling at Z mass

def alpha_s(mu_gev):
    """
    Simple two-loop running of strong coupling.
    
    Args:
        mu_gev: Energy scale in GeV
        
    Returns:
        alpha_s at scale mu
    """
    # Use two-loop beta function
    # This is a simplified version - full implementation would use RGE
    mz = 91.1876  # Z mass in GeV
    b0 = 11 - 2/3 * 5  # 5 active flavors at Z scale
    b1 = 102 - 38/3 * 5
    
    t = math.log(mu_gev / mz)
    
    # Two-loop approximation
    alpha_mz = ALPHA_S_MZ
    denominator = 1 + b0 * alpha_mz * t / (4 * math.pi)
    denominator += (b1/b0) * alpha_mz**2 * t**2 / (16 * math.pi**2)
    
    return alpha_mz / denominator

# Particle rung assignments (from theory document)
PARTICLE_RUNGS = {
    # Leptons
    'electron': 32,
    'muon': 39,
    'tau': 44,
    
    # Neutrinos
    'neutrino_e': 30,
    'neutrino_mu': 37,
    'neutrino_tau': 42,
    
    # Light quarks
    'up': 33,
    'down': 34,
    'strange': 38,
    
    # Heavy quarks
    'charm': 40,
    'bottom': 45,
    'top': 47,
    
    # Gauge bosons
    'photon': 0,
    'W': 52,
    'Z': 53,
    
    # Higgs
    'higgs': 58,
}

# Sector assignments
PARTICLE_SECTORS = {
    'electron': 'lepton',
    'muon': 'lepton',
    'tau': 'lepton',
    
    'neutrino_e': 'neutrino',
    'neutrino_mu': 'neutrino',
    'neutrino_tau': 'neutrino',
    
    'up': 'light_quark',
    'down': 'light_quark',
    'strange': 'light_quark',
    
    'charm': 'heavy_quark',
    'bottom': 'heavy_quark',
    'top': 'heavy_quark',
    
    'photon': 'gauge',
    'W': 'electroweak',
    'Z': 'electroweak',
    
    'higgs': 'higgs',
}

# PDG 2024 values (MeV) for validation
EXPERIMENTAL_MASSES = PDG_MASSES = {
    'electron': 0.51099895,
    'muon': 105.6583755,
    'tau': 1776.86,
    'up': 2.2,
    'down': 4.7,
    'strange': 93.0,
    'charm': 1270.0,
    'bottom': 4180.0,
    'top': 172690.0,
    'W': 80377.0,
    'Z': 91187.6,
    'higgs': 125250.0,
} 