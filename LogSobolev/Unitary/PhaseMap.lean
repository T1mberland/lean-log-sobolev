module

public import LogSobolev.Unitary.HilbertSchmidt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Normed.Lp.ProdLp

@[expose] public section

/-! # The metric estimate in Meckes–Meckes, Theorem 15

The phase map is defined on all of `ℝ × SU(N)`. Its restriction to the paper's
interval therefore needs no new metric estimate. `WithLp 2` is essential:
ordinary Lean products use the maximum metric, not the L² sum metric.
-/

open scoped Matrix.Norms.Frobenius NNReal
open Matrix

namespace LogSobolev

/-- The unit complex scalar `exp(i θ)`. -/
noncomputable def phase (θ : ℝ) : unitary ℂ :=
  ⟨Complex.exp (Complex.I * θ), by
    have hn : Complex.normSq (Complex.exp (Complex.I * θ)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_I_mul_ofReal, one_pow]
    constructor
    · simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hn,
        Complex.ofReal_one]
    · simp only [Complex.star_def, Complex.mul_conj, hn, Complex.ofReal_one]⟩

@[simp] theorem norm_phase (θ : ℝ) : ‖(phase θ : ℂ)‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal θ

/-- Chord length is at most arc length. -/
theorem phase_dist_le (s t : ℝ) : ‖(phase s : ℂ) - (phase t : ℂ)‖ ≤ |s - t| := by
  have he : (phase s : ℂ) - (phase t : ℂ) =
      (phase t : ℂ) * (Complex.exp (Complex.I * (s - t)) - 1) := by
    dsimp [phase]
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    congr 1
    ring
  rw [he, norm_mul, norm_phase, one_mul]
  simpa only [Complex.ofReal_sub, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A phase multiple of a unitary matrix is unitary. -/
noncomputable def phaseMul (a t : ℝ) (U : Matrix.unitaryGroup n ℂ) :
    Matrix.unitaryGroup n ℂ := phase (a * t) • U

/-- The elementary two-variable bound, valid on the whole unitary group. -/
theorem phaseMul_dist_le (a s t : ℝ) (U V : Matrix.unitaryGroup n ℂ) :
    dist (phaseMul a s U) (phaseMul a t V) ≤
      dist U V + (|a| * Real.sqrt (Fintype.card n)) * |s - t| := by
  rw [Subtype.dist_eq, dist_eq_norm]
  change ‖(phase (a * s) : ℂ) • (U : Matrix n n ℂ) -
      (phase (a * t) : ℂ) • (V : Matrix n n ℂ)‖ ≤ _
  calc
    _ ≤ ‖(phase (a * s) : ℂ) • ((U : Matrix n n ℂ) - V)‖ +
        ‖((phase (a * s) : ℂ) - phase (a * t)) • (V : Matrix n n ℂ)‖ := by
      convert norm_add_le ((phase (a * s) : ℂ) • ((U : Matrix n n ℂ) - V))
        (((phase (a * s) : ℂ) - phase (a * t)) • (V : Matrix n n ℂ)) using 1
      congr 1
      simp only [smul_sub, sub_smul]
      abel
    _ = dist U V + ‖(phase (a * s) : ℂ) - phase (a * t)‖ *
        Real.sqrt (Fintype.card n) := by
      simp only [norm_smul, norm_phase, one_mul, unitary_norm]
      rw [Subtype.dist_eq, dist_eq_norm]
    _ ≤ dist U V + |a * s - a * t| * Real.sqrt (Fintype.card n) :=
      add_le_add_right (mul_le_mul_of_nonneg_right (phase_dist_le _ _)
        (Real.sqrt_nonneg _)) _
    _ = _ := by rw [← mul_sub, abs_mul]; ring

/-- Cauchy–Schwarz in two real coordinates, in the exact form needed here. -/
theorem add_sqrt_two_mul_le (u v : ℝ) (_hu : 0 ≤ u) (_hv : 0 ≤ v) :
    u + Real.sqrt 2 * v ≤ Real.sqrt 3 * Real.sqrt (u ^ 2 + v ^ 2) := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have huv := Real.sq_sqrt (show 0 ≤ u ^ 2 + v ^ 2 by positivity)
  have hsq := sq_nonneg (Real.sqrt 2 * u - v)
  have hn : 0 ≤ Real.sqrt 3 * Real.sqrt (u ^ 2 + v ^ 2) := by positivity
  nlinarith [sq_nonneg (u + Real.sqrt 2 * v + Real.sqrt 3 * Real.sqrt (u ^ 2 + v ^ 2))]

/-- The paper's map into the actual unitary group. -/
noncomputable def phaseMap (N : ℕ) :
    WithLp 2 (ℝ × Matrix.specialUnitaryGroup (Fin N) ℂ) → Matrix.unitaryGroup (Fin N) ℂ :=
  fun p => phaseMul (Real.sqrt (2 / (N : ℝ))) p.fst ⟨p.snd.val, p.snd.prop.1⟩

/-- Exact formula for the map's matrix entries. -/
theorem phaseMap_apply (N : ℕ) (p : WithLp 2 (ℝ × Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    (phaseMap N p : Matrix (Fin N) (Fin N) ℂ) =
      Complex.exp (Complex.I * ((Real.sqrt (2 / (N : ℝ)) * p.fst : ℝ) : ℂ)) • p.snd.val := rfl

/-- The `sqrt(3)` Lipschitz estimate in the proof of Theorem 15.
This is an unconditional geometric theorem; it asserts no LSI or Haar decomposition. -/
theorem phaseMap_lipschitz (N : ℕ) (hN : 0 < N) :
    LipschitzWith ⟨Real.sqrt 3, Real.sqrt_nonneg 3⟩ (phaseMap N) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : |Real.sqrt (2 / (N : ℝ))| * Real.sqrt (Fintype.card (Fin N)) =
      Real.sqrt 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Fintype.card_fin,
      ← Real.sqrt_mul (div_nonneg (by norm_num) hNr.le), div_mul_cancel₀ _ hNr.ne']
  have h := phaseMul_dist_le (Real.sqrt (2 / (N : ℝ))) p.fst q.fst
    (⟨p.snd.val, p.snd.prop.1⟩ : Matrix.unitaryGroup (Fin N) ℂ)
    (⟨q.snd.val, q.snd.prop.1⟩ : Matrix.unitaryGroup (Fin N) ℂ)
  rw [hs] at h
  calc
    dist (phaseMap N p) (phaseMap N q) ≤ dist p.snd q.snd + Real.sqrt 2 * dist p.fst q.fst := by
      simpa only [phaseMap, Subtype.dist_eq, Real.dist_eq] using h
    _ ≤ Real.sqrt 3 * Real.sqrt (dist p.snd q.snd ^ 2 + dist p.fst q.fst ^ 2) :=
      add_sqrt_two_mul_le _ _ dist_nonneg dist_nonneg
    _ = _ := by
      rw [WithLp.prod_dist_eq_add (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, ← Real.sqrt_eq_rpow]
      rw [add_comm]
      rfl

end LogSobolev
