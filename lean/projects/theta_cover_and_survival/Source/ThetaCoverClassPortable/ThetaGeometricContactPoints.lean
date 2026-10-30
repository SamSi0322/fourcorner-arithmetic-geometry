import ThetaCoverClassPortable.ThetaVanishingDifferentialOrder
import ThetaCoverClassPortable.ThetaLinesPolynomialContacts
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces

namespace FourCorner.ThetaGeometricContactPoints
open AlgebraicGeometry AlgebraicCurve CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDGeometricChartPoints
open ThetaLinesContactPoints ThetaLinesPolynomialContacts
open SmoothProperRationalPointPlaces SchemePointStalkEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra

 theorem affine_relations (α β x : K) (hx : thetaF x 1 (α*x+β)=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![x,α*x+β] (ThetaDGeometricChartPoints.equation 1 a)=0 := by
  intro a;fin_cases a
  simpa [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc] using hx

 theorem vertical_relations (t x : K) (hx : thetaF (t*x) x 1=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![t*x,x] (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  intro a;fin_cases a
  simpa [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc] using hx

/-- These points land in the ACTUAL categorical Qbar pullback of original
D/Q, through its ORIGINAL rational chart quotient, not an unproved D(K) model. -/
def affinePoint (α β x : K) (hx : thetaF x 1 (α*x+β)=0) : RationalPoint toBase :=
  ⟨ThetaDGeometricChartPoints.point 1 ![x,α*x+β] (affine_relations α β x hx),
    ThetaDGeometricChartPoints.point_over _ _ _⟩

def verticalPoint (t x : K) (hx : thetaF (t*x) x 1=0) : RationalPoint toBase :=
  ⟨ThetaDGeometricChartPoints.point 2 ![t*x,x] (vertical_relations t x hx),
    ThetaDGeometricChartPoints.point_over _ _ _⟩

def affinePlace (α β x : K) (hx : thetaF x 1 (α*x+β)=0) : Place K field :=
  (pointEquivRationalPlace toBase (affinePoint α β x hx)).val

def verticalPlace (t x : K) (hx : thetaF (t*x) x 1=0) : Place K field :=
  (pointEquivRationalPlace toBase (verticalPoint t x hx)).val

 theorem affinePoint_injective (α β x y : K) (hx hy)
    (h : affinePoint α β x hx=affinePoint α β y hy) : x=y :=
  congrFun (ThetaDGeometricChartPoints.point_injective 1 _ _ _ _ (congrArg Subtype.val h)) 0

 theorem verticalPoint_injective (t x y : K) (hx hy)
    (h : verticalPoint t x hx=verticalPoint t y hy) : x=y :=
  congrFun (ThetaDGeometricChartPoints.point_injective 2 _ _ _ _ (congrArg Subtype.val h)) 1

 theorem affinePlace_injective (α β x y : K) (hx hy)
    (h : affinePlace α β x hx=affinePlace α β y hy) : x=y := by
  have he : pointEquivRationalPlace toBase (affinePoint α β x hx)=
      pointEquivRationalPlace toBase (affinePoint α β y hy) := Subtype.ext h
  exact affinePoint_injective α β x y hx hy ((pointEquivRationalPlace toBase).injective he)

 theorem verticalPlace_injective (t x y : K) (hx hy)
    (h : verticalPlace t x hx=verticalPlace t y hy) : x=y := by
  have he : pointEquivRationalPlace toBase (verticalPoint t x hx)=
      pointEquivRationalPlace toBase (verticalPoint t y hy) := Subtype.ext h
  exact verticalPoint_injective t x y hx hy ((pointEquivRationalPlace toBase).injective he)

/-- Full literal quartic factorization, with two distinct ACTUAL places
of the SAME original geometric curve and EXACT restriction multiplicities. -/
theorem affine_contacts (α β : K) (h : IsThetaSquareContact (.affine α β)) :
    ∃c x y : K,∃hx : thetaF x 1 (α*x+β)=0,∃hy : thetaF y 1 (α*y+β)=0,
      c≠0 ∧ x≠y ∧ affinePlace α β x hx≠affinePlace α β y hy ∧
      affineRestriction α β=Polynomial.C c*(Polynomial.X-Polynomial.C x)^2*(Polynomial.X-Polynomial.C y)^2 ∧
      (affineRestriction α β).rootMultiplicity x=2 ∧
      (affineRestriction α β).rootMultiplicity y=2 := by
  obtain ⟨c,a,b,d,hc,hd,he⟩ := (theta_no_hyperflex (.affine α β)).mp h
  have hn := affine_leading_ne_zero α β h
  have h4 : thetaA4 α β=c*a^2 := by simpa [ThetaLine.restrict,thetaF,thetaA4] using he 1 0
  have ha : a≠0 := by intro hz;apply hn;simpa [hz] using h4
  have hp := affine_square_polynomial α β c a b d he
  obtain ⟨x,y,hxy,hf,hmx,hmy⟩ := square_two_double_roots _ c a b d hc ha hd hp
  have hx : thetaF x 1 (α*x+β)=0 := by
    have hh := congrArg (Polynomial.eval x) hf
    simpa [affineRestriction,thetaF] using hh
  have hy : thetaF y 1 (α*y+β)=0 := by
    have hh := congrArg (Polynomial.eval y) hf
    simpa [affineRestriction,thetaF] using hh
  exact ⟨c*a^2,x,y,hx,hy,mul_ne_zero hc (pow_ne_zero _ ha),hxy,
    fun hg=>hxy (affinePlace_injective α β x y hx hy hg),hf,hmx,hmy⟩

 theorem vertical_contacts (t : K) (h : IsThetaSquareContact (.vertical t)) :
    ∃c x y : K,∃hx : thetaF (t*x) x 1=0,∃hy : thetaF (t*y) y 1=0,
      c≠0 ∧ x≠y ∧ verticalPlace t x hx≠verticalPlace t y hy ∧
      verticalRestriction t=Polynomial.C c*(Polynomial.X-Polynomial.C x)^2*(Polynomial.X-Polynomial.C y)^2 ∧
      (verticalRestriction t).rootMultiplicity x=2 ∧
      (verticalRestriction t).rootMultiplicity y=2 := by
  have hb := (theta_no_hyperflex (.vertical t)).mp h
  have hn := (theta_even_square_discriminant (by norm_num : (39984:K)≠0)
    ((theta_vertical_bitangent_iff t).mp hb)).1
  obtain ⟨c,a,b,d,hc,hd,he⟩ := hb
  have h4 : 9801*(t^4+1)+19598*t^2=c*a^2 := by simpa [ThetaLine.restrict,thetaF] using he 1 0
  have ha : a≠0 := by intro hz;apply hn;simpa [hz] using h4
  have hp := vertical_square_polynomial t c a b d he
  obtain ⟨x,y,hxy,hf,hmx,hmy⟩ := square_two_double_roots _ c a b d hc ha hd hp
  have hx : thetaF (t*x) x 1=0 := by
    have hh := congrArg (Polynomial.eval x) hf
    simpa [verticalRestriction,thetaF] using hh
  have hy : thetaF (t*y) y 1=0 := by
    have hh := congrArg (Polynomial.eval y) hf
    simpa [verticalRestriction,thetaF] using hh
  exact ⟨c*a^2,x,y,hx,hy,mul_ne_zero hc (pow_ne_zero _ ha),hxy,
    fun hg=>hxy (verticalPlace_injective t x y hx hy hg),hf,hmx,hmy⟩

#print axioms affinePlace_injective
#print axioms verticalPlace_injective
#print axioms affine_contacts
#print axioms vertical_contacts
end
end FourCorner.ThetaGeometricContactPoints
