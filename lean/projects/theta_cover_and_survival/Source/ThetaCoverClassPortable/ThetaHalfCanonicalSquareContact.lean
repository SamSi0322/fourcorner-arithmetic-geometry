import ThetaCoverClassPortable.ThetaRootOrderDoubleJets

namespace FourCorner.ThetaHalfCanonicalSquareContact
open AlgebraicGeometry AlgebraicCurve
open ThetaDGeometricModel ThetaLiteralBinaryRestrictions BinaryQuarticDoubleRoots
open ThetaRootCanonicalSections ThetaProjectiveRootPlaceEmbedding ThetaHalfCanonicalRootSupport
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem half_canonical_root_double (L : ThetaLine K) (B : Divisor K field)
    (hcan : canonicalDivisorOf (ThetaRootCanonicalSections.nonzero L)=(2:ℕ) • B) (P : Root L) :
    DoubleAt (restriction L) P.val := by
  apply ThetaRootOrderDoubleJets.root_double_at L P
  have hp := root_half_order_positive L B hcan P
  have he := congrArg (fun C : Divisor K field=>C (rootPlace L P)) hcan
  simp only [canonicalDivisorOf_apply,Finsupp.smul_apply,nsmul_eq_mul] at he
  omega

/-- A TRUE half-canonical divisor of the natural canonical plane section
forces an ordinary literal quadratic-square restriction. This treats all
line charts, both projective parameter charts, and repeated-place inputs. -/
theorem half_canonical_square_contact (L : ThetaLine K) (B : Divisor K field)
    (hcan : canonicalDivisorOf (ThetaRootCanonicalSections.nonzero L)=(2:ℕ) • B) :
    IsThetaSquareContact L := by
  obtain ⟨P,Q,hPQ,hP,hQ⟩ := ThetaRestrictionHasTwoRoots.two_projective_zeros L
  have hp := half_canonical_root_double L B hcan ⟨P,hP⟩
  have hq := half_canonical_root_double L B hcan ⟨Q,hQ⟩
  obtain ⟨c,a,b,d,hc,_,he⟩ := two_distinct_double_points (homogeneous L)
    (ThetaLiteralBinaryRestrictions.nonzero L) P Q hPQ hp hq
  exact square_of_polynomial_square L c a b d hc he

#print axioms half_canonical_root_double
#print axioms half_canonical_square_contact
end
end FourCorner.ThetaHalfCanonicalSquareContact
