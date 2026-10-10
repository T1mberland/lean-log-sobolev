import LogSobolev.Unitary.SpecialUnitaryPeak
import LogSobolev.Unitary.SpecialUnitaryPolynomialConvolution
import LogSobolev.Measure.PowerKernel

/-! # Concentrating polynomial probability densities on SU

Normalize natural powers of the degree-one peak `(N + Re Tr U)/(2N)`.
For positive dimension these are nonnegative polynomial densities of mass one
for the actual normalized Haar measure, and their mass outside every open
identity neighborhood tends to zero.
-/

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.Frobenius Manifold ContDiff Topology

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Normalized powers, represented in the actual degree-`j` polynomial space. -/
noncomputable def specialUnitaryPowerKernel (j : ℕ) : specialUnitaryPolynomialSpace (n := n) j :=
  ⟨(∫ U, specialUnitaryPeak.val U ^ j ∂specialUnitaryHaar n)⁻¹ • specialUnitaryPeak.val ^ j, by
    apply Submodule.smul_mem
    change specialUnitaryPeak.val ^ j ∈ specialUnitaryAffineSpace ^ j
    apply Submodule.pow_mem_pow
    have h := (specialUnitaryPeak (n := n)).prop
    change specialUnitaryPeak.val ∈ specialUnitaryAffineSpace ^ 1 at h
    rwa [pow_one (specialUnitaryAffineSpace (n := n))] at h⟩

/-- The polynomial kernel is exactly the normalized-power density. -/
theorem specialUnitaryPowerKernel_apply (j : ℕ) (U : Matrix.specialUnitaryGroup n ℂ) :
    (specialUnitaryPowerKernel j).val U =
      powerKernel (specialUnitaryHaar n) specialUnitaryPeak.val j U := by
  change (∫ V, specialUnitaryPeak.val V ^ j ∂specialUnitaryHaar n)⁻¹ *
    (specialUnitaryPeak.val ^ j) U = _
  simp only [ContMDiffMap.coe_pow, Pi.pow_apply, powerKernel, div_eq_mul_inv, mul_comm]

/-- Each polynomial density is nonnegative. -/
theorem specialUnitaryPowerKernel_nonneg (j : ℕ) (U : Matrix.specialUnitaryGroup n ℂ) :
    0 ≤ (specialUnitaryPowerKernel j).val U := by
  rw [specialUnitaryPowerKernel_apply]
  exact powerKernel_nonneg _ specialUnitaryPeak_nonneg j U

/-- Its normalization denominator is strictly positive for positive dimension. -/
theorem specialUnitaryPeak_integral_pow_pos (hN : 0 < Fintype.card n) (j : ℕ) :
    0 < ∫ U, specialUnitaryPeak.val U ^ j ∂specialUnitaryHaar n :=
  integral_pow_pos _ specialUnitaryPeak.val.contMDiff.continuous specialUnitaryPeak_nonneg
    (by rw [specialUnitaryPeak_one hN]; norm_num) j

/-- The polynomial density has mass exactly one. -/
theorem specialUnitaryPowerKernel_integral (hN : 0 < Fintype.card n) (j : ℕ) :
    (∫ U, (specialUnitaryPowerKernel j).val U ∂specialUnitaryHaar n) = 1 := by
  simp_rw [specialUnitaryPowerKernel_apply]
  exact integral_powerKernel _ (specialUnitaryPeak_integral_pow_pos hN j)

/-- Mass outside any open identity neighborhood vanishes. -/
theorem specialUnitaryPowerKernel_concentrates (hN : 0 < Fintype.card n)
    {s : Set (Matrix.specialUnitaryGroup n ℂ)} (hs : IsOpen s) (h1 : 1 ∈ s) :
    Tendsto (fun j => ∫ U in sᶜ, (specialUnitaryPowerKernel j).val U ∂specialUnitaryHaar n)
      atTop (𝓝 0) := by
  simp_rw [specialUnitaryPowerKernel_apply]
  exact tendsto_integral_powerKernel_compl_zero _ specialUnitaryPeak.val.contMDiff.continuous
    specialUnitaryPeak_nonneg (specialUnitaryPeak_one hN) (specialUnitaryPeak_lt_one hN) hs h1

end LogSobolev
