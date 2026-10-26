import HasseTangentUTransfer
import HasseSignAlgebra
namespace FourCorner.HasseTangentScaling
open HasseRationalSource HasseAnchorChoice HasseTangentGlobal HasseSignAlgebra

def scalePoint (p : ℚ) (P : HomogeneousPoint p) (s : ℚ) (hs : s ≠ 0) : HomogeneousPoint p where
  Z := s*P.Z
  U := s*P.U
  V := s*P.V
  W := s*P.W
  T := s*P.T
  nonzero := by
    rintro ⟨hz,hu,hv,hw,ht⟩
    exact P.nonzero ⟨(mul_eq_zero.mp hz).resolve_left hs,(mul_eq_zero.mp hu).resolve_left hs,
      (mul_eq_zero.mp hv).resolve_left hs,(mul_eq_zero.mp hw).resolve_left hs,(mul_eq_zero.mp ht).resolve_left hs⟩
  equations := by
    refine ⟨?_,?_,?_⟩
    · linear_combination s^2*P.equations.1
    · linear_combination s^2*P.equations.2.1
    · linear_combination s^2*P.equations.2.2

def scaleTangentData (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P)
    (s : ℚ) (hs : s ≠ 0) : TangentData p (scalePoint p P s hs) where
  w := s*D.w
  sign := by rcases D.sign with h | h <;> simp only [scalePoint,h,mul_neg] <;> tauto
  omission := by
    change CompleteSource11.OmitU p (s*P.Z) (s*P.V) (s*D.w) (s*P.T)
    refine ⟨?_,?_⟩
    · linear_combination s^2*D.omission.1
    · linear_combination s^2*D.omission.2
  separated := by
    have he : separation p (s*P.Z) (s*D.w) (s*P.T)=s^2*separation p P.Z D.w P.T := by
      dsimp [separation,anchorZ,anchorT]
      ring
    change separation p (s*P.Z) (s*D.w) (s*P.T) ≠ 0
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ hs) D.separated
  coefficient_negative := by
    have he : -p*secondPolar p (s*P.Z) (s*P.U) (s*P.T) (s*P.Z) (s*D.w) (s*P.T)=
        s^2*(-p*secondPolar p P.Z P.U P.T P.Z D.w P.T) := by
      dsimp [secondPolar,anchorU,anchorT,anchorZ]
      ring
    change -p*secondPolar p (s*P.Z) (s*P.U) (s*P.T) (s*P.Z) (s*D.w) (s*P.T)<0
    rw [he]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hs) D.coefficient_negative

theorem secondCoefficient_scale (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P)
    (s : ℚ) (hs : s ≠ 0) :
    secondCoefficient p (scalePoint p P s hs) (scaleTangentData p P D s hs)=secondCoefficient p P D*s^2 := by
  dsimp [secondCoefficient,scalePoint,scaleTangentData,secondPolar,anchorU,anchorT,anchorZ]
  ring

/-- Full scaling independence for the actual constructed rational sign, at
every place and for all nonzero rational scales, including denominators. -/
theorem tangentSign_scale (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P)
    (s : ℚ) (hs : s ≠ 0) (v : ℕ) :
    tangentSign p hp (scalePoint p P s hs) (scaleTangentData p P D s hs) v=tangentSign p hp P D v := by
  unfold tangentSign
  simp only [secondCoefficient_scale]
  exact rationalSign_mul_square_right _ _ s _ _ hs v

#print axioms scalePoint
#print axioms scaleTangentData
#print axioms secondCoefficient_scale
#print axioms tangentSign_scale
end FourCorner.HasseTangentScaling
