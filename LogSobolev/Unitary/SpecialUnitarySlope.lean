module

public import LogSobolev.Geometry.LocalSlopeDerivative
public import LogSobolev.Unitary.SpecialUnitaryFlow
public import LogSobolev.Unitary.SpecialUnitaryGenerator

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Actual SU derivatives and the Hilbert–Schmidt local slope

Left translation is an isometry for the unnormalized Frobenius metric.
The verified exponential curves and the scalar derivative–slope identity
therefore bound actual invariant derivatives by the paper's local metric slope.
-/

open Matrix
open scoped Matrix.Norms.Frobenius Manifold ContDiff ENNReal NNReal

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Left multiplication on SU preserves the unnormalized Hilbert–Schmidt distance. -/
theorem specialUnitary_isometry_mul_left (U : Matrix.specialUnitaryGroup n ℂ) :
    Isometry (fun V : Matrix.specialUnitaryGroup n ℂ => U * V) := by
  apply isometry_iff_dist_eq.mpr
  intro V W
  simp only [Subtype.dist_eq, dist_eq_norm, Submonoid.coe_mul]
  change ‖U.val * V.val - U.val * W.val‖ = ‖V.val - W.val‖
  rw [← mul_sub]
  exact norm_unitary_mul (specialUnitaryInclusion U) _

/-- The translated exponential curve has the exact Hilbert–Schmidt Lipschitz bound. -/
theorem specialUnitary_mul_exp_lipschitz
    (U : Matrix.specialUnitaryGroup n ℂ) (A : specialUnitaryLieAlgebra (n := n)) :
    LipschitzWith ‖A.val‖₊ (fun t => U * specialUnitaryExpCurve A t) := by
  simpa only [one_mul, Function.comp_def] using
    (specialUnitary_isometry_mul_left U).lipschitz.comp (specialUnitaryExpCurve_lipschitz A)

/-- Actual invariant derivatives are bounded by the upper local Hilbert–Schmidt slope.
The extended-real statement is valid even when the local slope is infinite. -/
theorem specialUnitaryDeriv_le_localSlope
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) (A : specialUnitaryLieAlgebra (n := n)) :
    ENNReal.ofReal ‖specialUnitaryDeriv A f U‖ ≤ (‖A.val‖₊ : ℝ≥0∞) * localSlope f U := by
  have hd := specialUnitary_hasDerivAt_mul_exp A U hf 0
  simp only [specialUnitaryExpCurve_zero, mul_one] at hd
  have h := localSlope_comp_le (specialUnitary_mul_exp_lipschitz U A) f 0
  simp only [Function.comp_def] at h
  rw [localSlope_eq_of_hasDerivAt hd] at h
  simpa only [specialUnitaryExpCurve_zero, mul_one] using h

variable {ι : Type*} [Fintype ι]

/-- The actual invariant gradient coordinates in a real Hilbert–Schmidt orthonormal basis. -/
noncomputable def specialUnitaryGradient
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    (f : Matrix.specialUnitaryGroup n ℂ → ℝ) (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryLieAlgebra (n := n) :=
  b.repr.symm (WithLp.toLp 2 (fun i => specialUnitaryDeriv (b i) f U))

/-- The squared HS norm of these gradient coordinates is the actual carré du champ. -/
theorem specialUnitaryGradient_norm_sq
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    ‖specialUnitaryGradient b f U‖ ^ 2 = specialUnitaryGamma b f f U := by
  rw [specialUnitaryGradient, b.repr.symm.norm_map, PiLp.norm_sq_eq_of_L2,
    specialUnitaryGamma_eq b hf hf]
  simp only [Real.norm_eq_abs]
  simp only [sq_abs]
  simp only [pow_two]

/-- Differentiating in the gradient direction gives the squared gradient norm. -/
theorem specialUnitaryDeriv_gradient
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    specialUnitaryDeriv (specialUnitaryGradient b f U) f U = specialUnitaryGamma b f f U := by
  rw [specialUnitaryGamma_eq b hf hf]
  unfold specialUnitaryGradient specialUnitaryDeriv
  rw [← b.sum_repr_symm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl

/-- Actual smooth energy is bounded pointwise by the paper's upper local HS slope squared. -/
theorem specialUnitaryGamma_le_localSlope_sq
    (b : OrthonormalBasis ι ℝ (specialUnitaryLieAlgebra (n := n)))
    {f : Matrix.specialUnitaryGroup n ℂ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, specialUnitaryLieAlgebra (n := n)) 𝓘(ℝ) ∞ f)
    (U : Matrix.specialUnitaryGroup n ℂ) :
    ENNReal.ofReal (specialUnitaryGamma b f f U) ≤ localSlope f U ^ 2 := by
  by_cases hs : localSlope f U = ⊤
  · simp [hs]
  have hd := specialUnitaryDeriv_le_localSlope hf U (specialUnitaryGradient b f U)
  rw [specialUnitaryDeriv_gradient b hf, Real.norm_of_nonneg (specialUnitaryGamma_nonneg b hf U)] at hd
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hs) hd
  simp only [ENNReal.toReal_ofReal (specialUnitaryGamma_nonneg b hf U),
    ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm] at hr
  change specialUnitaryGamma b f f U ≤ ‖specialUnitaryGradient b f U‖ * (localSlope f U).toReal at hr
  have hn := specialUnitaryGradient_norm_sq b hf U
  have hnorm : ‖specialUnitaryGradient b f U‖ ≤ (localSlope f U).toReal := by
    by_cases hz : ‖specialUnitaryGradient b f U‖ = 0
    · simp only [hz]
      exact ENNReal.toReal_nonneg
    · rw [← hn, pow_two] at hr
      exact le_of_mul_le_mul_left hr (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))
  rw [← hn, ENNReal.ofReal_pow (norm_nonneg _)]
  apply pow_le_pow_left' _ 2
  exact (ENNReal.ofReal_le_iff_le_toReal hs).mpr hnorm

end LogSobolev
