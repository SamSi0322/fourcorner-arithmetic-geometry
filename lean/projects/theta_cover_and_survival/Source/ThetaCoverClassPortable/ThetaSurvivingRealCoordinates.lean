import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Path
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
namespace FourCorner.ThetaSurvivingRealCoordinates

/-- The literal z=1 affine chart of the three quadrics of C, with
coordinates (P,Q,R,T). The scheme-point comparison is a separate step. -/
abbrev Chart := {v : Fin 4 → ℝ //
  v 0 ^ 2 = 1 + 50 * v 3 ^ 2 ∧
  v 1 ^ 2 = 1 + 14 * v 3 + 51 * v 3 ^ 2 ∧
  v 2 ^ 2 = 1 - 14 * v 3 + 51 * v 3 ^ 2}

theorem radicands_positive (t : ℝ) :
    0 < 1 + 50 * t^2 ∧
    0 < 1 + 14*t + 51*t^2 ∧
    0 < 1 - 14*t + 51*t^2 := by
  constructor
  · positivity
  constructor
  · nlinarith only [sq_nonneg (51*t + 7)]
  · nlinarith only [sq_nonneg (51*t - 7)]

def coordinates (t : ℝ) : Fin 4 → ℝ :=
  ![Real.sqrt (1 + 50*t^2), Real.sqrt (1 + 14*t + 51*t^2),
    Real.sqrt (1 - 14*t + 51*t^2), t]

theorem coordinates_on_curve (t : ℝ) :
    (coordinates t 0)^2 = 1 + 50*(coordinates t 3)^2 ∧
    (coordinates t 1)^2 = 1 + 14*(coordinates t 3) + 51*(coordinates t 3)^2 ∧
    (coordinates t 2)^2 = 1 - 14*(coordinates t 3) + 51*(coordinates t 3)^2 := by
  exact ⟨Real.sq_sqrt (radicands_positive t).1.le,
    Real.sq_sqrt (radicands_positive t).2.1.le,
    Real.sq_sqrt (radicands_positive t).2.2.le⟩

def chartPoint (t : ℝ) : Chart := ⟨coordinates t, coordinates_on_curve t⟩

theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [coordinates] <;> fun_prop

theorem chartPoint_continuous : Continuous chartPoint :=
  coordinates_continuous.subtype_mk _

theorem origin_coordinates : (chartPoint 0).val = ![1,1,1,0] := by
  ext i
  fin_cases i <;> norm_num [chartPoint, coordinates]

theorem endpoint_coordinates : (chartPoint 6).val =
    ![Real.sqrt 1801, Real.sqrt 1921, Real.sqrt 1753, 6] := by
  ext i
  fin_cases i <;> norm_num [chartPoint, coordinates]

/-- A path entirely inside the literal z=1 chart, from the rational boundary
coordinates to the point with affine T=1 coordinate z=1/6. -/
def positivePath : Path (chartPoint 0) (chartPoint 6) where
  toFun u := chartPoint (6*(u : ℝ))
  continuous_toFun := chartPoint_continuous.comp (continuous_const.mul continuous_subtype_val)
  source' := by norm_num
  target' := by norm_num

theorem path_nonboundary (u : unitInterval) (hu : 0 < (u : ℝ)) :
    0 < (positivePath u).val 3 := by
  change 0 < 6 * (u : ℝ)
  positivity

theorem endpoint_normalized_squares :
    (Real.sqrt 1801/6)^2 = ((1:ℝ)/6)^2 + 50 ∧
    (Real.sqrt 1921/6)^2 = ((1:ℝ)/6)^2 + 14*((1:ℝ)/6) + 51 ∧
    (Real.sqrt 1753/6)^2 = ((1:ℝ)/6)^2 - 14*((1:ℝ)/6) + 51 := by
  norm_num [div_pow, Real.sq_sqrt]

theorem endpoint_strict_metric :
    1 < Real.sqrt 1801 / 6 ∧
    0 < Real.sqrt 1921 / 6 ∧
    0 < Real.sqrt 1753 / 6 ∧
    Real.sqrt 1801 / 6 + 7 * |(1:ℝ)/6| < 50 := by
  have hp : 6 < Real.sqrt 1801 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hpu : Real.sqrt 1801 < 48 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hq : 0 < Real.sqrt 1921 := Real.sqrt_pos.2 (by norm_num)
  have hr : 0 < Real.sqrt 1753 := Real.sqrt_pos.2 (by norm_num)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 1/6)]
  exact ⟨by linarith, by positivity, by positivity, by linarith⟩

theorem endpoint_off_diagonal :
    (50 - Real.sqrt 1801/6 + 7*((1:ℝ)/6))/100 -
      (50 - Real.sqrt 1801/6 - 7*((1:ℝ)/6))/100 = 7/300 := by ring

end FourCorner.ThetaSurvivingRealCoordinates

#print axioms FourCorner.ThetaSurvivingRealCoordinates.positivePath
#print axioms FourCorner.ThetaSurvivingRealCoordinates.path_nonboundary
#print axioms FourCorner.ThetaSurvivingRealCoordinates.endpoint_normalized_squares
#print axioms FourCorner.ThetaSurvivingRealCoordinates.endpoint_strict_metric
#print axioms FourCorner.ThetaSurvivingRealCoordinates.endpoint_off_diagonal
