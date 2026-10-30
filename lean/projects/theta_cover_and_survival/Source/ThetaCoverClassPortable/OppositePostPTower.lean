import ThetaCoverClassPortable.MonicBoundaryRegular
import ThetaCoverClassPortable.OppositePostPChartScheme

noncomputable section
namespace FourCorner.OppositeProjective.PostPTower
open Polynomial OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev Base (K : Type u) [Field K] := Polynomial K
def a (mu nu : K) : Base K := C (A mu nu) - C (2*A mu nu*nu^2)*X^2
abbrev First (mu nu : K) := MonicBoundaryRegular.First (a mu nu)
abbrev z1 (mu nu : K) := AdjoinRoot.root (Multiquadratic.CoordinateAlgebra.equation₁ (Base K) (a mu nu))
abbrev t1 (mu nu : K) := algebraMap (Base K) (First mu nu) X

def b (mu nu : K) : First mu nu :=
  1 + algebraMap K (First mu nu) (mu^2) * (t1 mu nu)^2 + 2*z1 mu nu*t1 mu nu
def d (mu nu : K) : First mu nu :=
  1 + algebraMap K (First mu nu) (mu^2) * (t1 mu nu)^2 - 2*z1 mu nu*t1 mu nu
abbrev Tower (mu nu : K) := MonicBoundaryRegular.Tower (a mu nu) (b mu nu) (d mu nu)
abbrev t (mu nu : K) := algebraMap (Base K) (Tower mu nu) X
abbrev z (mu nu : K) := algebraMap (First mu nu) (Tower mu nu) (z1 mu nu)
abbrev q (mu nu : K) := Biquadratic.CoordinateAlgebra.coordinate₁ (First mu nu) (b mu nu) (d mu nu)
abbrev r (mu nu : K) := Biquadratic.CoordinateAlgebra.coordinate₂ (First mu nu) (b mu nu) (d mu nu)

lemma z1_sq (mu nu : K) : (z1 mu nu)^2 = algebraMap (Base K) (First mu nu) (a mu nu) := by
  have h := AdjoinRoot.eval₂_root (Multiquadratic.CoordinateAlgebra.equation₁ (Base K) (a mu nu))
  change (X^2-C (a mu nu) : (Base K)[X]).eval₂
    (AdjoinRoot.of _) (z1 mu nu) = 0 at h
  rw [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,sub_eq_zero] at h
  exact h

lemma originalRelations (mu nu : K) :
    (z mu nu)^2 - algebraMap K (Tower mu nu) (A mu nu) +
      2*algebraMap K (Tower mu nu) (A mu nu)*(algebraMap K (Tower mu nu) nu)^2*(t mu nu)^2 = 0 ∧
    (q mu nu)^2 - 1 - (algebraMap K (Tower mu nu) mu)^2*(t mu nu)^2 - 2*z mu nu*t mu nu = 0 ∧
    (r mu nu)^2 - 1 - (algebraMap K (Tower mu nu) mu)^2*(t mu nu)^2 + 2*z mu nu*t mu nu = 0 := by
  have hz : (z mu nu)^2 = algebraMap (Base K) (Tower mu nu) (a mu nu) := by
    rw [z, ← map_pow, z1_sq, ← IsScalarTower.algebraMap_apply]
  have hq := Biquadratic.CoordinateAlgebra.coordinate₁_sq (First mu nu) (b mu nu) (d mu nu)
  have hr := Biquadratic.CoordinateAlgebra.coordinate₂_sq (First mu nu) (b mu nu) (d mu nu)
  have hbase (c : K) : algebraMap (Base K) (Tower mu nu) (C c) = algebraMap K (Tower mu nu) c := by
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have hscalar (c : K) : algebraMap (First mu nu) (Tower mu nu) (algebraMap K (First mu nu) c) =
      algebraMap K (Tower mu nu) c := (IsScalarTower.algebraMap_apply _ _ _ c).symm
  have ht : algebraMap (First mu nu) (Tower mu nu) (t1 mu nu) = t mu nu := by
    rw [t1, ← IsScalarTower.algebraMap_apply]
  have ha : algebraMap (Base K) (Tower mu nu) (a mu nu) =
      algebraMap K (Tower mu nu) (A mu nu) -
        2*algebraMap K (Tower mu nu) (A mu nu)*(algebraMap K (Tower mu nu) nu)^2*(t mu nu)^2 := by
    change algebraMap (Base K) (Tower mu nu) (C (A mu nu) - C (2*A mu nu*nu^2)*X^2) = _
    rw [map_sub,map_mul,map_pow,hbase,hbase]
    simp only [map_mul,map_pow,map_ofNat]
  have hb : algebraMap (First mu nu) (Tower mu nu) (b mu nu) =
      1+(algebraMap K (Tower mu nu) mu)^2*(t mu nu)^2+2*z mu nu*t mu nu := by
    change algebraMap (First mu nu) (Tower mu nu)
      (1+algebraMap K (First mu nu) (mu^2)*(t1 mu nu)^2+2*z1 mu nu*t1 mu nu) = _
    simp only [map_add,map_one,map_mul,map_pow,map_ofNat,hscalar,ht]
  have hd : algebraMap (First mu nu) (Tower mu nu) (d mu nu) =
      1+(algebraMap K (Tower mu nu) mu)^2*(t mu nu)^2-2*z mu nu*t mu nu := by
    change algebraMap (First mu nu) (Tower mu nu)
      (1+algebraMap K (First mu nu) (mu^2)*(t1 mu nu)^2-2*z1 mu nu*t1 mu nu) = _
    simp only [map_add,map_sub,map_one,map_mul,map_pow,map_ofNat,hscalar,ht]
  rw [ha] at hz
  rw [hb] at hq
  rw [hd] at hr
  constructor
  · linear_combination hz
  constructor
  · linear_combination hq
  · linear_combination hr

/-- The boundary parameter T/P is a non-zero-divisor in the actual dependent monic tower. -/
theorem t_regular (mu nu : K) : IsRegular (t mu nu) :=
  MonicBoundaryRegular.tower_coordinate_regular (a mu nu) (b mu nu) (d mu nu) X
    (isRegular_of_ne_zero Polynomial.X_ne_zero)

end FourCorner.OppositeProjective.PostPTower
#print axioms FourCorner.OppositeProjective.PostPTower.originalRelations
#print axioms FourCorner.OppositeProjective.PostPTower.t_regular
