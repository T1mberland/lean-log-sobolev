module

public import LogSobolev

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Independent clients of the locally Lipschitz interval and U(1) results. -/
open MeasureTheory LogSobolev
open scoped Matrix.Norms.Frobenius

example (L : ℝ) (hL : 0 < L) (f : Set.Icc (0 : ℝ) L → ℝ)
    (hf : LocallyLipschitz f) :
    entropy (intervalUniform L) (fun t => f t ^ 2) ≤
      (L ^ 2 / 4) * ∫ t, (localSlope f t).toReal ^ 2 ∂intervalUniform L :=
  intervalUniform_entropy_sq_le_of_locallyLipschitz L hL hf

-- Distance to an interior point is admissible even at its nonsmooth zero.
example (L : ℝ) (hL : 0 < L) (a : Set.Icc (0 : ℝ) L) :
    entropy (intervalUniform L) (fun t => dist t a ^ 2) ≤
      (L ^ 2 / 4) * ∫ t, (localSlope (fun s => dist s a) t).toReal ^ 2
        ∂intervalUniform L :=
  intervalUniform_entropy_sq_le_of_locallyLipschitz L hL
    (LipschitzWith.dist_left a).locallyLipschitz

example : MetricLSI (unitaryHaar (Fin 1)) 6 := unitary_fin_one_metricLSI

example : entropy (unitaryHaar (Fin 1)) (fun U => dist U 1 ^ 2) ≤
    12 * ∫ U, (localSlope (fun V : Matrix.unitaryGroup (Fin 1) ℂ => dist V 1) U).toReal ^ 2
      ∂unitaryHaar (Fin 1) :=
  unitary_fin_one_entropy_sq_le
    (LipschitzWith.dist_left (1 : Matrix.unitaryGroup (Fin 1) ℂ)).locallyLipschitz

example : entropy (unitaryHaar (Fin 1)) (fun U => entryReal (0 : Fin 1) 0 U ^ 2) ≤
    12 * ∫ U, (localSlope (entryReal (0 : Fin 1) 0) U).toReal ^ 2 ∂unitaryHaar (Fin 1) :=
  unitary_fin_one_entropy_sq_le (entryReal_lipschitz 0 0).locallyLipschitz

example (c : ℝ) : ¬ entryReal (0 : Fin 1) 0 =ᵐ[unitaryHaar (Fin 1)] (fun _ => c) :=
  entryReal_not_ae_constant 0 c

example :
    Integrable (fun U => entryReal (0 : Fin 1) 0 U ^ 2) (unitaryHaar (Fin 1)) ∧
    Integrable (fun U => entryReal (0 : Fin 1) 0 U ^ 2 *
      Real.log (entryReal (0 : Fin 1) 0 U ^ 2)) (unitaryHaar (Fin 1)) ∧
    Integrable (fun U => (localSlope (entryReal (0 : Fin 1) 0) U).toReal ^ 2)
      (unitaryHaar (Fin 1)) :=
  unitary_regular (entryReal_lipschitz 0 0).locallyLipschitz
