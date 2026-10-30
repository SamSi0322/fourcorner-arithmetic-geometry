import ThetaCoverClassPortable.ThetaFiniteGenericDegree

namespace FourCorner.ThetaDActualFieldCover
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open ThetaLiteralModels ThetaDGeometricModel ThetaNativeFunctionFieldMap
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev sourceBase : coverSource ⟶ Spec (.of K) := coverMap ≫ toBase

def sourceMap : coverSource ⟶ ThetaSourceGenus.geometricScheme :=
  pullback.lift (pullback.fst projection (pullback.fst (dToBase ℚ) qb)) sourceBase (by
    rw [←projection_over,←Category.assoc,pullback.condition]
    simp only [sourceBase,coverMap,toBase,Category.assoc,pullback.condition])

def mapFromC : ThetaSourceGenus.geometricScheme ⟶ geometricD :=
  pullback.lift (pullback.fst (cToBase ℚ) qb ≫ projection) (pullback.snd (cToBase ℚ) qb) (by
    rw [Category.assoc,projection_over,pullback.condition])

def sourceInv : ThetaSourceGenus.geometricScheme ⟶ coverSource :=
  pullback.lift (pullback.fst (cToBase ℚ) qb) mapFromC (by simp [mapFromC])

def sourceIso : coverSource ≅ ThetaSourceGenus.geometricScheme where
  hom := sourceMap
  inv := sourceInv
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [sourceMap,sourceInv,Category.assoc]
    · apply pullback.hom_ext
      · simpa [sourceMap,sourceInv,mapFromC,Category.assoc] using
          (pullback.condition (f:=projection) (g:=pullback.fst (dToBase ℚ) qb))
      · simp [sourceMap,sourceInv,mapFromC,sourceBase,coverMap,toBase,Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [sourceMap,sourceInv,mapFromC,sourceBase,coverMap,toBase,Category.assoc]

theorem sourceIso_over : sourceIso.hom ≫ ThetaSourceGenus.geometricToBase=sourceBase := by
  simp [sourceIso,sourceMap,ThetaSourceGenus.geometricToBase]

theorem cover_finite : IsFinite coverMap := by
  letI := ThetaProjectionFiniteEtale.projection_finite
  infer_instance

theorem cover_etale : Etale coverMap := by
  letI := ThetaProjectionFiniteEtale.projection_etale
  infer_instance

theorem cover_rank (y : geometricD) : coverMap.finrank y=2 := by
  letI := ThetaProjectionFiniteEtale.projection_finite
  letI := ThetaProjectionFiniteEtale.projection_etale
  rw [Scheme.Hom.finrank_pullback_snd]
  exact ThetaProjectionDegree.projection_degree_two _

local instance : IsIntegral coverSource := cover_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Surjective coverMap := cover_surjective
local instance : Flat coverMap := cover_flat
local instance : IsFinite coverMap := cover_finite
local instance : Etale coverMap := cover_etale

abbrev F := geometricD.functionField
abbrev E := coverSource.functionField
abbrev fAlgebra : Algebra K F := (baseToFunctionField toBase).toAlgebra
abbrev eAlgebra : Algebra K E := (baseToFunctionField sourceBase).toAlgebra
abbrev extensionAlgebra : Algebra F E := (fieldMap coverMap).toAlgebra

theorem extension_tower :
    letI := fAlgebra;letI := eAlgebra;letI := extensionAlgebra;IsScalarTower K F E := by
  letI := fAlgebra;letI := eAlgebra;letI := extensionAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a => (base_compatibility coverMap sourceBase toBase rfl a).symm

/-- Degree TWO on the ACTUAL native function fields of the SAME original
geometric covering morphism. All scheme and generic diagrams are retained. -/
theorem extension_degree : letI := extensionAlgebra;Module.finrank F E=2 :=
  ThetaFiniteGenericDegree.degree_two coverMap cover_rank

theorem extension_finite : letI := extensionAlgebra;FiniteDimensional F E := by
  letI := extensionAlgebra
  exact Module.finite_of_finrank_pos (by rw [extension_degree];decide)

theorem source_proper : IsProper sourceBase := by
  letI := geometric_proper
  infer_instance

theorem source_smooth : SmoothOfRelativeDimension 1 sourceBase := by
  letI := geometric_smooth
  haveI : SmoothOfRelativeDimension 0 coverMap := inferInstance
  change SmoothOfRelativeDimension (0+1) (coverMap ≫ toBase)
  infer_instance

/-- Genus five transferred along the explicit actual over-K source iso. -/
theorem source_genus : letI := eAlgebra;genusFF K E=5 := by
  letI := eAlgebra
  letI := ThetaSourceGenus.geometric_integral
  letI := (baseToFunctionField ThetaSourceGenus.geometricToBase).toAlgebra
  let e := ThetaIsoFunctionField.algEquiv sourceBase ThetaSourceGenus.geometricToBase sourceIso sourceIso_over
  exact (genusFF_eq_of_algEquiv e).symm.trans ThetaSourceGenus.genus_five

#print axioms sourceIso_over
#print axioms extension_degree
#print axioms extension_finite
#print axioms source_genus
end
end FourCorner.ThetaDActualFieldCover
