import ThetaCoverClassPortable.OppositeUniformGeometricGenus
import ThetaCoverClassPortable.ThetaGeometricNativeModel

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaUniformGeometricGenus
open ThetaLiteralModels ThetaRationalPicardInput

abbrev XAt {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) := pullback (cToBase ℚ) y
abbrev cAt {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) := pullback.snd (cToBase ℚ) y

theorem integral_at {K : Type} [Field K] (y : Spec (.of K) ⟶ Spec (.of ℚ)) : IsIntegral (XAt y) := by
  letI := source_geometricallyIntegral
  exact GeometricallyIntegral.geometrically_isIntegral (f:=cToBase ℚ) y
    (pullback.fst (cToBase ℚ) y) (cAt y) (.of_hasPullback _ _)

variable (K : Type) [Field K] [Algebra ℚ K]
abbrev X := XAt (Scheme.TwoAffineOpenCover.specMap ℚ K)
abbrev c := cAt (Scheme.TwoAffineOpenCover.specMap ℚ K)
def baseIso : X K ≅ OppositeUniformGeometricGenus.X K :=
  ThetaSourceGenus.baseChangeIso (Scheme.TwoAffineOpenCover.specMap ℚ K)

theorem baseIso_over : (baseIso K).hom ≫ OppositeUniformGeometricGenus.c K=c K := by
  simp only [baseIso,ThetaSourceGenus.baseChangeIso,asIso_hom,pullback.map,pullback.lift_snd,Category.comp_id]

/-- Genus FIVE for every actual algebraically closed K-base change of the
ORIGINAL C/Q, via the constructed native function-field comparison. -/
theorem genus_five [IsAlgClosed K] :
    letI := integral_at (Scheme.TwoAffineOpenCover.specMap ℚ K)
    letI := (baseToFunctionField (c K)).toAlgebra
    genusFF K (X K).functionField=5 := by
  letI := integral_at (Scheme.TwoAffineOpenCover.specMap ℚ K)
  letI := OppositeUniformGeometricGenus.integral K
  letI := (baseToFunctionField (c K)).toAlgebra
  letI := (baseToFunctionField (OppositeUniformGeometricGenus.c K)).toAlgebra
  let e := ThetaIsoFunctionField.algEquiv (c K) (OppositeUniformGeometricGenus.c K) (baseIso K) (baseIso_over K)
  exact (genusFF_eq_of_algEquiv e).symm.trans (OppositeUniformGeometricGenus.genus_five K)

/-- ALL actual field-valued maps to Spec Q, not only a selected Qbar fibre.
No external Algebra Q K or characteristic-zero hypothesis is added. -/
theorem actual_genus_five {K : Type} [Field K] [IsAlgClosed K]
    (y : Spec (.of K) ⟶ Spec (.of ℚ)) :
    letI := integral_at y
    letI := (baseToFunctionField (cAt y)).toAlgebra
    genusFF K (XAt y).functionField=5 := by
  obtain ⟨a,ha⟩ := Spec.map_surjective y
  letI : Algebra ℚ K := a.hom.toAlgebra
  have hy : y=Scheme.TwoAffineOpenCover.specMap ℚ K := ThetaSourceComparison.rational_base_unique _ _
  subst y
  exact genus_five K

#print axioms genus_five
#print axioms actual_genus_five
end FourCorner.ThetaUniformGeometricGenus
