module

public import LogSobolev.Unitary.SpecialUnitary
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section

/-! # Full-circle Haar decomposition of the unitary group

Scalar multiplication is a continuous surjective homomorphism from
`Circle × SU(N)` to `U(N)` in positive dimension. Consequently it sends the
product of Haar probabilities to Haar probability. This is the full-circle
version of Meckes–Meckes Lemma 16; reducing the phase to the short interval
is a separate obligation.
-/

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace LogSobolev

/-- Regard a point on the complex unit circle as a unitary scalar. -/
def circleUnitary (z : Circle) : unitary ℂ :=
  ⟨z, by
    constructor
    · simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Circle.normSq_coe, Complex.ofReal_one]
    · simp only [Complex.star_def, Complex.mul_conj, Circle.normSq_coe,
        Complex.ofReal_one]⟩

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Multiplication by a scalar phase, as a homomorphism on `Circle × SU`. -/
def circleSpecialUnitaryMap :
    Circle × Matrix.specialUnitaryGroup n ℂ →* Matrix.unitaryGroup n ℂ where
  toFun p := circleUnitary p.1 • specialUnitaryInclusion p.2
  map_one' := by apply Subtype.ext; simp [circleUnitary]
  map_mul' p q := by
    apply Subtype.ext
    change ((p.1 : ℂ) * (q.1 : ℂ)) • (p.2.val * q.2.val) =
      ((p.1 : ℂ) • p.2.val) * ((q.1 : ℂ) • q.2.val)
    simp [smul_smul, mul_comm]

/-- Exact scalar-matrix formula. -/
theorem circleSpecialUnitaryMap_apply (p : Circle × Matrix.specialUnitaryGroup n ℂ) :
    (circleSpecialUnitaryMap p : Matrix n n ℂ) = (p.1 : ℂ) • p.2.val := rfl

theorem circleSpecialUnitaryMap_continuous :
    Continuous (circleSpecialUnitaryMap :
      Circle × Matrix.specialUnitaryGroup n ℂ → Matrix.unitaryGroup n ℂ) := by
  change Continuous (fun p : Circle × Matrix.specialUnitaryGroup n ℂ =>
    (⟨(p.1 : ℂ) • p.2.val, _⟩ : Matrix.unitaryGroup n ℂ))
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

/-- Every circle element admits an Nth root on the circle, for positive N. -/
theorem circle_exists_pow (z : Circle) (N : ℕ) (hN : 0 < N) :
    ∃ w : Circle, w ^ N = z := by
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (z : ℂ)).mp (Circle.norm_coe z)
  refine ⟨Circle.exp (θ / N), ?_⟩
  rw [← Circle.exp_natCast_mul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [mul_div_cancel₀ θ hNr]
  exact Circle.ext hθ

/-- The full-circle phase map is onto the actual U group. -/
theorem circleSpecialUnitaryMap_surjective (hn : 0 < Fintype.card n) :
    Function.Surjective (circleSpecialUnitaryMap :
      Circle × Matrix.specialUnitaryGroup n ℂ → Matrix.unitaryGroup n ℂ) := by
  intro U
  have hd : ‖(U.val).det‖ = 1 := by
    exact CStarRing.norm_coe_unitary (⟨U.val.det, Matrix.det_of_mem_unitary U.prop⟩ : unitary ℂ)
  let d : Circle := ⟨U.val.det, by exact mem_sphere_zero_iff_norm.mpr hd⟩
  obtain ⟨z, hz⟩ := circle_exists_pow d (Fintype.card n) hn
  have hz' : (z : ℂ) ^ Fintype.card n = U.val.det := congrArg (fun w : Circle => (w : ℂ)) hz
  let V : Matrix.unitaryGroup n ℂ := circleUnitary z⁻¹ • U
  have hV : V.val.det = 1 := by
    change Matrix.det (((z⁻¹ : Circle) : ℂ) • U.val) = 1
    rw [Matrix.det_smul]
    rw [Circle.coe_inv, inv_pow, hz', inv_mul_cancel₀]
    exact (Matrix.UnitaryGroup.det_isUnit U).ne_zero
  refine ⟨(z, ⟨V.val, V.prop, hV⟩), ?_⟩
  apply Subtype.ext
  change (z : ℂ) • (((z⁻¹ : Circle) : ℂ) • U.val) = U.val
  rw [smul_smul, Circle.coe_inv, mul_inv_cancel₀ (Circle.coe_ne_zero z), one_smul]

noncomputable instance circleMeasurableSpace : MeasurableSpace Circle := borel _
instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- Normalized Haar measure on the complex unit circle. -/
noncomputable def circleHaar : Measure Circle := Measure.haarMeasure ⊤

instance : Measure.IsHaarMeasure circleHaar := by
  unfold circleHaar
  infer_instance

instance : IsProbabilityMeasure circleHaar where
  measure_univ := Measure.haarMeasure_self

/-- A uniform circle phase times an independent Haar SU matrix is Haar on U.
This does not yet identify the smaller phase interval used in Lemma 16. -/
theorem map_circleSpecialUnitaryMap (hn : 0 < Fintype.card n) :
    Measure.map circleSpecialUnitaryMap (circleHaar.prod (specialUnitaryHaar n)) =
      unitaryHaar n := by
  have hm := (circleSpecialUnitaryMap_continuous (n := n)).measurable
  letI := isMulLeftInvariant_map
    (μ := circleHaar.prod (specialUnitaryHaar n))
    circleSpecialUnitaryMap.toMulHom hm (circleSpecialUnitaryMap_surjective hn)
  exact eq_unitaryHaar _

/-- A central scalar matrix belongs to SU when its dimension power is one. -/
def specialUnitaryScalar (z : Circle) (hz : z ^ Fintype.card n = 1) :
    Matrix.specialUnitaryGroup n ℂ :=
  ⟨(z : ℂ) • (1 : Matrix n n ℂ),
    (circleUnitary z • (1 : Matrix.unitaryGroup n ℂ)).prop, by
      change Matrix.det ((z : ℂ) • (1 : Matrix n n ℂ)) = 1
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact congrArg (fun w : Circle => (w : ℂ)) hz⟩

/-- Multiplication by a central root of unity preserves SU Haar probability. -/
theorem specialUnitaryHaar_map_scalar (z : Circle) (hz : z ^ Fintype.card n = 1) :
    Measure.map (fun V => specialUnitaryScalar z hz * V) (specialUnitaryHaar n) =
      specialUnitaryHaar n :=
  map_mul_left_eq_self _ _

/-- Multiplying a fixed scalar phase by a central Nth root does not change
its SU-Haar mixture. This is the finite-rotation step in the short-interval
Haar decomposition. -/
theorem map_circleSpecialUnitaryMap_mul_root (w z : Circle)
    (hz : z ^ Fintype.card n = 1) :
    Measure.map (fun V : Matrix.specialUnitaryGroup n ℂ =>
      circleSpecialUnitaryMap (w * z, V)) (specialUnitaryHaar n) =
    Measure.map (fun V : Matrix.specialUnitaryGroup n ℂ =>
      circleSpecialUnitaryMap (w, V)) (specialUnitaryHaar n) := by
  have hm : Measurable (fun V : Matrix.specialUnitaryGroup n ℂ =>
      circleSpecialUnitaryMap (w, V)) :=
    (circleSpecialUnitaryMap_continuous.comp (continuous_const.prodMk continuous_id)).measurable
  calc
    _ = Measure.map (fun V : Matrix.specialUnitaryGroup n ℂ =>
        circleSpecialUnitaryMap (w, V))
        (Measure.map (fun V => specialUnitaryScalar z hz * V) (specialUnitaryHaar n)) := by
      rw [Measure.map_map hm (measurable_const_mul _)]
      congr 1
      funext V
      apply Subtype.ext
      change ((w : ℂ) * (z : ℂ)) • V.val =
        (w : ℂ) • (((z : ℂ) • (1 : Matrix n n ℂ)) * V.val)
      simp [smul_smul]
    _ = _ := by rw [specialUnitaryHaar_map_scalar]

end LogSobolev
