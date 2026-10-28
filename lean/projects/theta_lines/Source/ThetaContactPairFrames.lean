import ThetaCanonicalLinePointValues

namespace FourCorner.ThetaContactPairFrames
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDActualDifferential
open ThetaRegularFunctionDifferential ThetaDGlobalCanonicalCandidate ThetaDPlaneRegularForms
open ThetaGeometricContactPoints ThetaContactDifferentialDivisors ThetaContactTangencyCertificates
open ThetaAffineContactOrder ThetaVerticalContactOrder ThetaActualLineDifferentials
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem double_divisor_orders {η : Ω[field⁄K]} (hη : η≠0) (P Q : Place K field) (hpq : P≠Q)
    (hdiv : canonicalDivisorOf hη=Finsupp.single P 2+Finsupp.single Q 2) :
    P.ordDifferential η=2 ∧ Q.ordDifferential η=2 := by
  have hP := congrArg (fun D : Divisor K field=>D P) hdiv
  have hQ := congrArg (fun D : Divisor K field=>D Q) hdiv
  rw [canonicalDivisorOf_apply] at hP hQ
  exact ⟨by simpa [hpq] using hP,by simpa [hpq.symm] using hQ⟩

/-- Degree4 exactness makes the ACTUAL local canonical frame a unit at the
contact, instead of assuming a canonical-plane/nonhyperelliptic property. -/
theorem frame_order_zero (w : Place K field) (f : field) (ζ η : Ω[field⁄K])
    (hf : f≠0) (hζ : ζ≠0) (he : η=f • ζ)
    (hηord : w.ordDifferential η=2) (hford : 2≤w.ord f) (hζord : 0≤w.ordDifferential ζ) :
    w.ordDifferential ζ=0 := by
  have hh := w.ordDifferential_smul hf (ThetaContactDifferentialDivisors.coefficient_ne_zero hζ w)
  rw [←he] at hh
  omega

 theorem affine_pair_frames (α β : K) (h : IsThetaSquareContact (.affine α β)) :
    ∃x y : K,∃hx : thetaF x 1 (α*x+β)=0,∃hy : thetaF y 1 (α*y+β)=0,
      x≠y ∧ affinePlace α β x hx≠affinePlace α β y hy ∧
      canonicalDivisorOf (affineDifferential_ne_zero α β)=
        Finsupp.single (affinePlace α β x hx) 2+Finsupp.single (affinePlace α β y hy) 2 ∧
      (affinePlace α β x hx).ordDifferential (ThetaDFieldCoordinates.y • omega)=0 ∧
      (affinePlace α β y hy).ordDifferential (ThetaDFieldCoordinates.y • omega)=0 := by
  obtain ⟨c,x,y,hx,hy,hc,hxy,hpq,hf,_,_⟩ := affine_contacts α β h
  have hdx : (ThetaLinesPolynomialContacts.affineRestriction α β).derivative.eval x=0 := by
    rw [hf];exact factored_derivative_zero c x y
  have hdy : (ThetaLinesPolynomialContacts.affineRestriction α β).derivative.eval y=0 := by
    have he : ThetaLinesPolynomialContacts.affineRestriction α β=
        Polynomial.C c*(Polynomial.X-Polynomial.C y)^2*(Polynomial.X-Polynomial.C x)^2 := by rw [hf];ring
    rw [he];exact factored_derivative_zero c y x
  have hdiv := canonical_two_double_zeros (affineDifferential_ne_zero α β)
    (germ_orders_nonnegative (affineGlobalSection α β)) _ _ hpq
    (affine_differential_contact_order α β x hx hdx) (affine_differential_contact_order α β y hy hdy)
  have hord := double_divisor_orders (affineDifferential_ne_zero α β) _ _ hpq hdiv
  have hn : ThetaDFieldCoordinates.y • omega≠0 :=
    smul_ne_zero ThetaActualLineDifferentials.y_ne_zero omega_ne_zero
  have he : affineDifferential α β=affineFunction α β • (ThetaDFieldCoordinates.y • omega) :=
    affineGlobalSection_germ α β
  refine ⟨x,y,hx,hy,hxy,hpq,hdiv,?_,?_⟩
  · exact frame_order_zero _ _ _ _ (affineFunction_ne_zero α β) hn he hord.1
      (affine_function_order_ge_two α β x hx hdx)
      ((affinePlace α β x hx).ord_nonneg_of_mem (yomega_coefficient_regular _))
  · exact frame_order_zero _ _ _ _ (affineFunction_ne_zero α β) hn he hord.2
      (affine_function_order_ge_two α β y hy hdy)
      ((affinePlace α β y hy).ord_nonneg_of_mem (yomega_coefficient_regular _))

 theorem vertical_pair_frames (t : K) (h : IsThetaSquareContact (.vertical t)) :
    ∃x y : K,∃hx : thetaF (t*x) x 1=0,∃hy : thetaF (t*y) y 1=0,
      x≠y ∧ verticalPlace t x hx≠verticalPlace t y hy ∧
      canonicalDivisorOf (verticalDifferential_ne_zero t)=
        Finsupp.single (verticalPlace t x hx) 2+Finsupp.single (verticalPlace t y hy) 2 ∧
      (verticalPlace t x hx).ordDifferential omega=0 ∧
      (verticalPlace t y hy).ordDifferential omega=0 := by
  obtain ⟨c,x,y,hx,hy,hc,hxy,hpq,hf,_,_⟩ := vertical_contacts t h
  have hdx : (ThetaLinesPolynomialContacts.verticalRestriction t).derivative.eval x=0 := by
    rw [hf];exact factored_derivative_zero c x y
  have hdy : (ThetaLinesPolynomialContacts.verticalRestriction t).derivative.eval y=0 := by
    have he : ThetaLinesPolynomialContacts.verticalRestriction t=
        Polynomial.C c*(Polynomial.X-Polynomial.C y)^2*(Polynomial.X-Polynomial.C x)^2 := by rw [hf];ring
    rw [he];exact factored_derivative_zero c y x
  have hdiv := canonical_two_double_zeros (verticalDifferential_ne_zero t)
    (germ_orders_nonnegative (verticalGlobalSection t)) _ _ hpq
    (vertical_differential_contact_order t x hx hdx) (vertical_differential_contact_order t y hy hdy)
  have hord := double_divisor_orders (verticalDifferential_ne_zero t) _ _ hpq hdiv
  have he : verticalDifferential t=verticalFunction t • omega := verticalGlobalSection_germ t
  refine ⟨x,y,hx,hy,hxy,hpq,hdiv,?_,?_⟩
  · exact frame_order_zero _ _ _ _ (verticalFunction_ne_zero t) omega_ne_zero he hord.1
      (vertical_function_order_ge_two t x hx hdx) (all_orders_nonnegative _)
  · exact frame_order_zero _ _ _ _ (verticalFunction_ne_zero t) omega_ne_zero he hord.2
      (vertical_function_order_ge_two t y hy hdy) (all_orders_nonnegative _)

#print axioms frame_order_zero
#print axioms affine_pair_frames
#print axioms vertical_pair_frames
end
end FourCorner.ThetaContactPairFrames
