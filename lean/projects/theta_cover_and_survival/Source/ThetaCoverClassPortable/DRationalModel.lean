import ThetaCoverClassPortable.DSinglePoleModel

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.DRationalInputs
local instance instIsIntegralCurve_dRationalModel : IsIntegral curve := integral
local instance instIsProperToBase_dRationalModel : IsProper toBase := proper
local instance instSmoothOfRelativeDimensionOfNatNatToBase_dRationalModel : SmoothOfRelativeDimension 1 toBase := smooth
local instance instAlgebraRatField_dRationalModel : Algebra ℚ field := constants

/-- A genuine field model for QQ(D), with an actual over-QQ iso from the
original D and the exact native generic-Spec diagram. -/
theorem exists_native_model :
    ∃ M : CurveModel ℚ field, ∃ i : curve ≅ M.C,
      i.hom ≫ M.toBase = toBase ∧
      curve.fromSpecStalk (genericPoint curve) ≫ i.hom =
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
  obtain ⟨f,r,hf,hr,hpole,haway,ht,hfd⟩ := single_origin_poles 0
  letI := hfd
  obtain ⟨i,hi,hg⟩ := singlePole_model_comparison f ht
  exact ⟨singlePoleModel f ht, i, hi, hg⟩

end FourCorner.DRationalInputs
