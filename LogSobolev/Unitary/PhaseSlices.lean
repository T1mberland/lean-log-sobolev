module

public import LogSobolev.Unitary.PhaseMap
public import LogSobolev.Unitary.SpecialUnitary
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Phase slices with their exact metric constants

Fixing the special unitary coordinate gives speed `sqrt(2)` in the paper's
phase parameter, for the unnormalized Hilbert–Schmidt metric. The resulting
family of continuous SU observables is Lipschitz in the uniform norm.
-/

open Matrix
open scoped Matrix.Norms.Frobenius NNReal

namespace LogSobolev

/-- The paper's phase curve at a fixed unitary matrix has speed at most `sqrt(2)`. -/
theorem phaseMul_sqrt_lipschitz (N : ℕ) (hN : 0 < N)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    LipschitzWith ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩
      (fun t => phaseMul (Real.sqrt (2 / (N : ℝ))) t U) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : |Real.sqrt (2 / (N : ℝ))| * Real.sqrt (Fintype.card (Fin N)) =
      Real.sqrt 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Fintype.card_fin,
      ← Real.sqrt_mul (div_nonneg (by norm_num) hNr.le), div_mul_cancel₀ _ hNr.ne']
  apply LipschitzWith.of_dist_le_mul
  intro s t
  change dist (phaseMul (Real.sqrt (2 / (N : ℝ))) s U)
    (phaseMul (Real.sqrt (2 / (N : ℝ))) t U) ≤ Real.sqrt 2 * dist s t
  simpa only [dist_self, zero_add, hs, Real.dist_eq] using
    phaseMul_dist_le (Real.sqrt (2 / (N : ℝ))) s t U U

/-- A fixed phase preserves the HS distance exactly. -/
theorem phaseMul_isometry {n : Type*} [Fintype n] [DecidableEq n] (a t : ℝ) :
    Isometry (phaseMul (n := n) a t) := by
  apply Isometry.of_dist_eq
  intro U V
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖(phase (a * t) : ℂ) • (U : Matrix n n ℂ) -
    (phase (a * t) : ℂ) • (V : Matrix n n ℂ)‖ = ‖(U : Matrix n n ℂ) - V‖
  rw [← smul_sub, norm_smul, norm_phase, one_mul]

/-- Restriction of a continuous U(N) observable to a translated SU(N) slice. -/
noncomputable def unitaryPhaseSlice (N : ℕ)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℝ)) (t : ℝ) :
    C(Matrix.specialUnitaryGroup (Fin N) ℂ, ℝ) :=
  ⟨fun V => f (phaseMul (Real.sqrt (2 / (N : ℝ))) t (specialUnitaryInclusion V)),
    f.continuous.comp ((phaseMul_isometry _ _).continuous.comp
      specialUnitaryInclusion_isometry.continuous)⟩

/-- The phase family is Lipschitz in the uniform norm, simultaneously on all SU points. -/
theorem unitaryPhaseSlice_lipschitz (N : ℕ) (hN : 0 < N)
    (f : C(Matrix.unitaryGroup (Fin N) ℂ, ℝ)) {K : NNReal} (hf : LipschitzWith K f) :
    LipschitzWith (K * ⟨Real.sqrt 2, Real.sqrt_nonneg 2⟩) (unitaryPhaseSlice N f) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro V
  exact (hf.comp (phaseMul_sqrt_lipschitz N hN (specialUnitaryInclusion V))).dist_le_mul s t

end LogSobolev
