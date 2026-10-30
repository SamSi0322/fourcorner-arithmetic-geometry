import ThetaCoverClassPortable.DCurveAffineNeighborhoods
import ThetaCoverClassPortable.DReducedBaseInputs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
namespace FourCorner.DRationalInputs
open ThetaLiteralModels AlgebraicGeometry.RelPicard

/-- The exact CURVE-relative affine-neighbourhood input for the universal
relative-divisor construction, on actual original D after any ring basechange.
It is not AF/projectivity of a represented Picard space. -/
theorem actual_curve_relative_affines (T : Type) [CommRing T] [Algebra ℚ T]
    (V : (Spec (.of T)).affineOpens)
    (F : Finset (pullback (C:=Scheme) toBase (SmoothProperCurve.specMap ℚ T)))
    (hF : ∀x∈F,SmoothProperCurve.baseChange ℚ toBase T x∈(V:(Spec (.of T)).Opens)) :
    ∃ U : (pullback (C:=Scheme) toBase (SmoothProperCurve.specMap ℚ T)).Opens,
      IsAffineOpen U ∧ U≤SmoothProperCurve.baseChange ℚ toBase T ⁻¹ᵁ (V:(Spec (.of T)).Opens) ∧
        ∀x∈F,x∈U :=
  DCurveAffineNeighborhoods.relative_affine_basechange (SmoothProperCurve.specMap ℚ T) V.1 V.2 F hF

/-- The SAME actual finite-etale base supplies hF/hgamma AND the exact curve
hcov needed for relative-divisor parameter schemes. No open charts or
representation are assumed or claimed by this family-prerequisite statement. -/
theorem actual_family_with_curve_relative_affines :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra ℚ R') (_ : Module.Finite ℚ R')
      (_ : Algebra.Etale ℚ R') (_ : Module.FaithfullyFlat ℚ R')
      (_ : IsNoetherianRing R') (_ : _root_.IsReduced R'),
      let cR := SmoothProperCurve.baseChange ℚ toBase R'
      let εR := SmoothProperCurve.sectionBaseChange R' OD
      IsProper cR ∧ SmoothOfRelativeDimension 1 cR ∧ GeometricallyIntegral cR ∧
      (∀m0:ℕ,∃F:SmoothProperCurve.FiniteMapData cR εR,m0≤F.m ∧IsUnit (F.m:R')) ∧
      ∃ (n:ℕ) (γ:Fin n→Fin (7-3)→SchemeHomOver (𝟙 _) cR),
        HasChartSections (g:=3) (r:=7) cR γ ∧
        ∀ (V:(Spec (.of R')).affineOpens)
          (F:Finset (pullback (C:=Scheme) toBase (SmoothProperCurve.specMap ℚ R'))),
          (∀x∈F,cR x∈(V:(Spec (.of R')).Opens)) →
          ∃ U:(pullback (C:=Scheme) toBase (SmoothProperCurve.specMap ℚ R')).Opens,
            IsAffineOpen U ∧U≤cR ⁻¹ᵁ (V:(Spec (.of R')).Opens) ∧∀x∈F,x∈U := by
  obtain ⟨R',_,_,_,_,_,_,_,hp,hs,hgi,hF,n,γ,hγ⟩ := actual_reduced_base_family_inputs
  refine ⟨R',inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,hp,hs,hgi,hF,n,γ,hγ,?_⟩
  intro V F hF
  exact actual_curve_relative_affines R' V F hF

#print axioms actual_curve_relative_affines
#print axioms actual_family_with_curve_relative_affines
end FourCorner.DRationalInputs
