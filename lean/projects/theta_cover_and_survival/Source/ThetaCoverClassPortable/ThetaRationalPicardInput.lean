import ThetaCoverClassPortable.ThetaQuotient
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.SchemePointStalkEvaluation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels ThetaActualPoints

/-- The actual accepted rational origin, over the actual structural map. -/
def OC : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of ℚ))) (cToBase ℚ) :=
  ⟨originC, boundaryPoint_over (fun _ => true)⟩

theorem source_proper : IsProper (cToBase ℚ) := c_proper ℚ
theorem source_smooth : SmoothOfRelativeDimension 1 (cToBase ℚ) := ThetaSourceSmooth.source_smooth

/-- Geometric integrality of the actual original C over Q, proved for every
field-valued base change via the accepted literal comparison. -/
theorem source_geometricallyIntegral : GeometricallyIntegral (cToBase ℚ) := by
  haveI := OppositeProjective.ExactGenus.geometricallyIntegral (1:ℚ) 5
    (by norm_num) (by norm_num) (by norm_num)
  constructor
  intro L _ y Z fst snd hpb
  haveI := GeometricallyIntegral.geometrically_isIntegral (f:=ThetaSourceGenus.oppositeBase) y
    (CategoryTheory.Limits.pullback.fst ThetaSourceGenus.oppositeBase y)
    (CategoryTheory.Limits.pullback.snd ThetaSourceGenus.oppositeBase y) (.of_hasPullback _ _)
  haveI : IsIntegral (CategoryTheory.Limits.pullback (cToBase ℚ) y) :=
    IsIntegral.of_isIso (ThetaSourceGenus.baseChangeIso y).inv
  exact IsIntegral.of_isIso hpb.isoPullback.inv

/-- The actual rational origin has a closed image, without fictitious Pic1 data. -/
theorem origin_closedImmersion : IsClosedImmersion OC.1 :=
  isClosedImmersion_of_comp_eq_id (cToBase ℚ) OC.1 OC.2

def originComplement : (C ℚ).Opens := by
  letI := origin_closedImmersion
  exact ⟨(Set.range OC.1)ᶜ, OC.1.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[simp] theorem mem_originComplement (x : C ℚ) :
    x ∈ originComplement ↔ x ∉ Set.range OC.1 := Iff.rfl

/-- A genuine FiniteMapData MUST use exactly this single-origin complement. -/
theorem finiteMapData_U (F : SmoothProperCurve.FiniteMapData (cToBase ℚ) OC) :
    F.U = originComplement := by
  ext x
  exact F.mem_U_iff x

private def otherSigns : Fin 3 → Bool := fun _ => false
private def otherPoint : Spec (.of ℚ) ⟶ C ℚ := boundaryPoint otherSigns
private def otherCentre : C ℚ := otherPoint (IsLocalRing.closedPoint ℚ)

private theorem other_not_origin : otherCentre ∉ Set.range OC.1 := by
  rintro ⟨x,hx⟩
  have hc : otherCentre = originC (IsLocalRing.closedPoint ℚ) := by
    rw [←hx]
    exact congrArg OC.1 (Subsingleton.elim _ _)
  have he : boundaryPoint (k:=ℚ) otherSigns = boundaryPoint (fun _ => true) :=
    SchemePointStalkEvaluation.point_ext (cToBase ℚ) _ _ (boundaryPoint_over otherSigns)
      (boundaryPoint_over (fun _ => true)) hc
  have hh := congrFun (boundaryPoint_injective (k:=ℚ) he) 0
  contradiction

private theorem other_not_tOpen : otherCentre ∉ ThetaBoundary.tOpen (k:=ℚ) := by
  have h := ThetaBoundary.boundaryPoint_boundary (k:=ℚ) otherSigns
  have hx : IsLocalRing.closedPoint ℚ ∉
      (boundaryPoint (k:=ℚ) otherSigns) ⁻¹ᵁ ThetaBoundary.tOpen := by
    rw [h]
    simp
  exact hx

/-- The rank-eight z/T affine chart excludes eight boundary points and
therefore cannot be the U required by FiniteMapData for the actual OC. -/
theorem originComplement_ne_tOpen : originComplement ≠ ThetaBoundary.tOpen (k:=ℚ) := by
  intro h
  have hx : otherCentre ∈ originComplement := other_not_origin
  rw [h] at hx
  exact other_not_tOpen hx

theorem finiteMapData_U_ne_tOpen (F : SmoothProperCurve.FiniteMapData (cToBase ℚ) OC) :
    F.U ≠ ThetaBoundary.tOpen (k:=ℚ) := by
  rw [finiteMapData_U F]
  exact originComplement_ne_tOpen

#print axioms OC
#print axioms source_geometricallyIntegral
#print axioms origin_closedImmersion
#print axioms finiteMapData_U
#print axioms originComplement_ne_tOpen
#print axioms finiteMapData_U_ne_tOpen
end FourCorner.ThetaRationalPicardInput
