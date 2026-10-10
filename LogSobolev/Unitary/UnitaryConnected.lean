import LogSobolev.Geometry.FiniteSpectrumUnitary
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # Connectedness of the actual finite-dimensional unitary group

The C⋆ operator norm is used only to apply functional calculus. Its topology is
the standard finite matrix topology, shared with the Frobenius metric. The
conclusion mentions only that topology and introduces no change of metric.
-/

open scoped Matrix.Norms.L2Operator

namespace LogSobolev

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every finite-dimensional complex unitary group is connected. -/
instance unitaryConnectedSpace : ConnectedSpace (Matrix.unitaryGroup n ℂ) := by
  letI : CStarAlgebra (Matrix n n ℂ) := { }
  exact unitary_connectedSpace_of_finite_spectrum (A := Matrix n n ℂ)
    (fun U => Matrix.finite_spectrum U.val)

end LogSobolev
