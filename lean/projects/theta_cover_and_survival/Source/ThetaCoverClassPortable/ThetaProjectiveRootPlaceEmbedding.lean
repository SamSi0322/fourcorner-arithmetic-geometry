import ThetaCoverClassPortable.ThetaLineRootPointCharts

namespace FourCorner.ThetaProjectiveRootPlaceEmbedding
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaLiteralBinaryRestrictions ThetaLineRootPointCharts BinaryQuarticDoubleRoots
open SmoothProperRationalPointPlaces
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra

 def finiteParameter (P : P1 K) (h : P≠infinity) : K :=
  Classical.choose ((point_charts P).resolve_left h)

 theorem finiteParameter_spec (P : P1 K) (h : P≠infinity) : P=finitePoint (finiteParameter P h) :=
  Classical.choose_spec ((point_charts P).resolve_left h)

 theorem infinity_equation (L : ThetaLine K) (P : P1 K) (hz : ZeroAt (restriction L) P) (h : P=infinity) :
    L.restrict 1 0=0 := by
  have he := (zeroAt_infinity_iff (homogeneous L)).mp (h ▸ hz)
  rw [eval_restriction] at he
  exact he

 theorem finite_equation (L : ThetaLine K) (P : P1 K) (hz : ZeroAt (restriction L) P) (h : P≠infinity) :
    L.restrict (finiteParameter P h) 1=0 := by
  have hP := finiteParameter_spec P h
  have he := (zeroAt_finite_iff (homogeneous L) (finiteParameter P h)).mp (hP ▸ hz)
  rw [eval_restriction] at he
  exact he

/-- Map from a TRUE native P1 zero to an ACTUAL over-K point of original
categorical D_Qbar. Finite and infinity charts are both retained. -/
def rootPoint (L : ThetaLine K) (P : P1 K) (hz : ZeroAt (restriction L) P) : RationalPoint toBase :=
  if h : P=infinity then infinityRootPoint L (infinity_equation L P hz h)
  else finiteRootPoint L (finiteParameter P h) (finite_equation L P hz h)

 theorem rootPoint_injective (L : ThetaLine K) (P Q : P1 K)
    (hP : ZeroAt (restriction L) P) (hQ : ZeroAt (restriction L) Q)
    (he : rootPoint L P hP=rootPoint L Q hQ) : P=Q := by
  by_cases hPi : P=infinity
  · by_cases hQi : Q=infinity
    · exact hPi.trans hQi.symm
    · have hn := infinityRootPoint_ne_finite L (finiteParameter Q hQi)
        (infinity_equation L P hP hPi) (finite_equation L Q hQ hQi)
      exact False.elim (hn (by simpa only [rootPoint,dif_pos hPi,dif_neg hQi] using he))
  · by_cases hQi : Q=infinity
    · have hn := infinityRootPoint_ne_finite L (finiteParameter P hPi)
        (infinity_equation L Q hQ hQi) (finite_equation L P hP hPi)
      exact False.elim (hn (by simpa only [rootPoint,dif_pos hQi,dif_neg hPi] using he.symm))
    · have hval : finiteParameter P hPi=finiteParameter Q hQi :=
        finiteRootPoint_injective L _ _ _ _ (by simpa only [rootPoint,dif_neg hPi,dif_neg hQi] using he)
      exact (finiteParameter_spec P hPi).trans ((congrArg finitePoint hval).trans (finiteParameter_spec Q hQi).symm)

abbrev Root (L : ThetaLine K) := {P : P1 K // ZeroAt (restriction L) P}

def rootPlace (L : ThetaLine K) (P : Root L) : Place K field :=
  (pointEquivRationalPlace toBase (rootPoint L P.val P.property)).val

/-- Injectivity uses the actual point-place equivalence and actual scheme
chart maps, not an injection of candidate labels. It also separates infinity
from finite points by the genuine original standard open. -/
theorem rootPlace_injective (L : ThetaLine K) : Function.Injective (rootPlace L) := by
  intro P Q h
  have he : pointEquivRationalPlace toBase (rootPoint L P.val P.property)=
      pointEquivRationalPlace toBase (rootPoint L Q.val Q.property) := Subtype.ext h
  apply Subtype.ext
  exact rootPoint_injective L P.val Q.val P.property Q.property ((pointEquivRationalPlace toBase).injective he)

#print axioms infinity_equation
#print axioms finite_equation
#print axioms rootPoint_injective
#print axioms rootPlace_injective
end
end FourCorner.ThetaProjectiveRootPlaceEmbedding
