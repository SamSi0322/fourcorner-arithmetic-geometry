import ThetaCoverClassPortable.ThetaDChartPlaceRegularity

namespace FourCorner.ThetaDChartNaturality
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open ThetaLiteralModels ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaNativeFunctionFieldMap
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral (D ℚ) := original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra

 theorem qb_surjective : Surjective qb := by
  constructor
  intro q
  exact ⟨(⊥ : PrimeSpectrum K),Subsingleton.elim _ _⟩
local instance : Surjective qb := qb_surjective
local instance : Surjective (pullback.fst (dToBase ℚ) qb) := inferInstance

theorem U_nonempty (j : Fin 3) : Nonempty (U j) := by
  obtain ⟨p⟩ := geoU_nonempty j
  exact ⟨⟨pullback.fst (dToBase ℚ) qb p.val,p.property⟩⟩
local instance (j : Fin 3) : Nonempty (U j) := U_nonempty j
local instance (j : Fin 3) : Nonempty (geoU j) := geoU_nonempty j

/-- Generic germs commute with the ACTUAL generic-stalk map of a dominant
morphism. This is a structural-sheaf identity, not a coordinate assumption. -/
theorem generic_germ_naturality {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Surjective f] (V : Y.Opens) [Nonempty V]
    [Nonempty (f ⁻¹ᵁ V)] (s : Γ(Y,V)) :
    fieldMap f (Y.germToFunctionField V s)=
      X.germToFunctionField (f ⁻¹ᵁ V) ((f.app V).hom s) := by
  have hx : genericPoint X ∈ f ⁻¹ᵁ V :=
    ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ V).isOpen).mpr (by simpa using (inferInstance : Nonempty (f ⁻¹ᵁ V)))
  rw [←Y.algebraMap_germ_eq_germToFunctionField hx s,
    ThetaEtaleAllPlaces.stalk_field_naturality]
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact X.algebraMap_germ_eq_germToFunctionField hx _

local instance originalSectionsAlgebra (j : Fin 3) : Algebra ℚ Γ(D ℚ,U j) :=
  Scheme.TwoAffineOpenCover.algebraOfHom (dToBase ℚ) (U j)
local instance geoSectionsAlgebra (j : Fin 3) : Algebra K Γ(geometricD,geoU j) :=
  Scheme.TwoAffineOpenCover.algebraOfHom toBase (geoU j)

 theorem actualChartEquiv_one_tmul (j : Fin 3) (r : chartRing j) :
    actualChartEquiv j (1 ⊗ₜ[ℚ] r)=
      ((pullback.fst (dToBase ℚ) qb).app (U j)).hom ((sectionsAlgEquiv j).symm r) := by
  change P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv
    (dToBase ℚ) K (U j) (affine_U j) (tensorSectionsEquiv j (1 ⊗ₜ[ℚ] r))=_
  have ht : tensorSectionsEquiv j (1 ⊗ₜ[ℚ] r)=
      (1:K) ⊗ₜ[ℚ] (sectionsAlgEquiv j).symm r := rfl
  rw [ht]
  exact P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange.algEquiv_one_tmul
    (dToBase ℚ) K (U j) (affine_U j) _

/-- The literal coordinates already constructed in the native geometric
field are EXACTLY the pullbacks of the original rational chart germs. -/
theorem chartToField_one_tmul (j : Fin 3) (r : chartRing j) :
    chartToField j (1 ⊗ₜ[ℚ] r)=
      fieldMap (pullback.fst (dToBase ℚ) qb)
        ((D ℚ).germToFunctionField (U j) ((sectionsAlgEquiv j).symm r)) := by
  change geometricD.germToFunctionField (geoU j) (actualChartEquiv j (1 ⊗ₜ[ℚ] r))=_
  rw [actualChartEquiv_one_tmul]
  letI : Nonempty (pullback.fst (dToBase ℚ) qb ⁻¹ᵁ U j) := geoU_nonempty j
  exact (generic_germ_naturality _ (U j) _).symm

#print axioms qb_surjective
#print axioms generic_germ_naturality
#print axioms actualChartEquiv_one_tmul
#print axioms chartToField_one_tmul
end
end FourCorner.ThetaDChartNaturality
