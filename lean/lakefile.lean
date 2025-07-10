import Lake
open Lake DSL

package «ledger-particle-masses» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ParticleMasses» where
  -- Main particle masses library

lean_lib «VacuumPolarization» where
  -- Vacuum polarization theory

lean_lib «VacuumPolarizationNumerical» where
  -- Numerical computations for vacuum polarization

lean_lib «MinimalNumerical» where
  -- Minimal numerical verification

lean_lib «SimpleNumerical» where
  -- Simple numerical verification approach
