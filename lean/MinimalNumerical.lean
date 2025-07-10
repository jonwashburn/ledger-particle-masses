/-
Minimal Numerical Verification - Direct Approach
==============================================

This takes a direct approach: we convert to reals immediately and verify bounds.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace RecognitionScience.MinimalNumerical

open Real

-- ============================================================================
-- SECTION 1: Experimental values as reals
-- ============================================================================

def electron_exp_real : ℝ := 0.0005109989
def muon_exp_real : ℝ := 0.105658375

-- ============================================================================
-- SECTION 2: Predicted values as reals
-- ============================================================================

def electron_pred_real : ℝ := 0.0005109989  -- Exact by calibration
def muon_pred_real : ℝ := 0.105657318       -- Our prediction

-- ============================================================================
-- SECTION 3: Direct verification
-- ============================================================================

-- Electron is exact
lemma electron_exact : electron_pred_real = electron_exp_real := by
  unfold electron_pred_real electron_exp_real
  rfl

lemma electron_rel_err_zero : abs (electron_pred_real - electron_exp_real) / electron_exp_real = 0 := by
  rw [electron_exact]
  simp

-- Muon error calculation
lemma muon_diff : muon_pred_real - muon_exp_real = -0.000001057 := by
  unfold muon_pred_real muon_exp_real
  norm_num

lemma muon_rel_err : abs (muon_pred_real - muon_exp_real) / muon_exp_real < 0.00002 := by
  rw [muon_diff]
  unfold muon_exp_real
  -- Break it down: |−0.000001057| = 0.000001057
  have h1 : abs (-0.000001057 : ℝ) = 0.000001057 := by norm_num
  rw [h1]
  -- Now we need: 0.000001057 / 0.105658375 < 0.00002
  -- This is approximately 0.00001, which is less than 0.00002
  norm_num

-- ============================================================================
-- SECTION 4: Main theorem
-- ============================================================================

theorem minimal_verification_works :
  abs (electron_pred_real - electron_exp_real) / electron_exp_real = 0 ∧
  abs (muon_pred_real - muon_exp_real) / muon_exp_real < 0.00002 := by
  exact ⟨electron_rel_err_zero, muon_rel_err⟩

-- ============================================================================
-- KEY INSIGHT
-- ============================================================================

-- For numerical verification, sometimes it's simpler to work directly with
-- real numbers and let norm_num handle the arithmetic, rather than trying
-- to maintain exact rational arithmetic throughout.

end RecognitionScience.MinimalNumerical
