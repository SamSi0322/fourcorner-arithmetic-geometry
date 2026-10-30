import ThetaCoverClassPortable.ThetaGaloisSchemeField
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaGaloisFieldAction
open ThetaDGeometricModel ThetaLiteralModels ThetaNativeFunctionFieldMap NativeFunctionFieldFunctor
open ThetaGaloisSchemeField SmoothProperRationalPointPlaces
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : Surjective qb := ThetaDChartNaturality.qb_surjective
local instance : Surjective (pullback.fst (dToBase ℚ) qb) := inferInstance

theorem fieldAut_one : fieldAut (1:Gal)=1 := by
  ext a
  change fieldMap (schemeMap (1:Gal)) a=a
  simpa only [schemeMap_one,fieldMap_id,RingHom.id_apply]

 theorem fieldAut_mul (σ ρ : Gal) : fieldAut (σ*ρ)=fieldAut σ*fieldAut ρ := by
  ext a
  change fieldMap (schemeMap (σ*ρ)) a=fieldMap (schemeMap σ) (fieldMap (schemeMap ρ) a)
  simpa only [schemeMap_mul,fieldMap_comp,RingHom.comp_apply]

/-- The actual absolute-Galois action through generic STALKS, bundled as
the true semilinear group homomorphism, not chosen from a coordinate basis. -/
def absoluteAction : Gal →* SemilinearAut K field where
  toFun := semilinear
  map_one' := Subtype.ext (Prod.ext fieldAut_one rfl)
  map_mul' σ ρ := Subtype.ext (Prod.ext (fieldAut_mul σ ρ) rfl)

 theorem fieldAut_rational_image (σ : Gal) (a : (D ℚ).functionField) :
    fieldAut σ (fieldMap (pullback.fst (dToBase ℚ) qb) a)=
      fieldMap (pullback.fst (dToBase ℚ) qb) a := by
  change fieldMap (schemeMap σ) (fieldMap (pullback.fst (dToBase ℚ) qb) a)=_
  have hh:=congrArg (fun φ=>φ a) (fieldMap_comp (schemeMap σ) (pullback.fst (dToBase ℚ) qb))
  simp only [schemeMap_fst] at hh
  exact hh.symm

 theorem fieldAut_coordinate (σ : Gal) (j : Fin 3) (a : Fin 2) :
    fieldAut σ (ThetaDFieldCoordinates.coordinate j a)=ThetaDFieldCoordinates.coordinate j a := by
  rw [ThetaDExactChartTransitions.coordinate_eq_native_ratio]
  exact fieldAut_rational_image σ _

 theorem fieldAut_x (σ : Gal) : fieldAut σ ThetaDFieldCoordinates.x=ThetaDFieldCoordinates.x :=
  fieldAut_coordinate σ 2 0

 theorem fieldAut_y (σ : Gal) : fieldAut σ ThetaDFieldCoordinates.y=ThetaDFieldCoordinates.y :=
  fieldAut_coordinate σ 2 1

 theorem baseScheme_one : baseScheme (1:Gal)=𝟙 (Spec (.of K)) := by
  change Spec.map (𝟙 (CommRingCat.of K))=𝟙 _
  simp

 theorem schemeMap_inv (σ : Gal) : schemeMap σ⁻¹=inv (schemeMap σ) := by
  apply (cancel_epi (schemeMap σ)).mp
  rw [←schemeMap_mul,mul_inv_cancel,schemeMap_one,IsIso.hom_inv_id]

/-- Correct LEFT action on actual over-K points: Spec(sigma) on the source,
then the point, then the INVERSE actual basechange Scheme automorphism. -/
def pointMap (σ : Gal) (p : RationalPoint toBase) : RationalPoint toBase :=
  ⟨baseScheme σ ≫ p.val ≫ schemeMap σ⁻¹,by
    simp only [Category.assoc,schemeMap_snd]
    rw [←Category.assoc p.val toBase _,p.property,Category.id_comp,
      ←baseScheme_mul,mul_inv_cancel,baseScheme_one]⟩

 theorem pointMap_actual_inverse (σ : Gal) (p : RationalPoint toBase) :
    (pointMap σ p).val=baseScheme σ ≫ p.val ≫ inv (schemeMap σ) := by
  change baseScheme σ ≫ p.val ≫ schemeMap σ⁻¹=baseScheme σ ≫ p.val ≫ inv (schemeMap σ)
  rw [schemeMap_inv]

 theorem pointMap_one (p : RationalPoint toBase) : pointMap (1:Gal) p=p := by
  apply Subtype.ext
  simp [pointMap,baseScheme_one,schemeMap_one]

 theorem pointMap_mul (σ ρ : Gal) (p : RationalPoint toBase) :
    pointMap (σ*ρ) p=pointMap σ (pointMap ρ p) := by
  apply Subtype.ext
  simp only [pointMap,baseScheme_mul,mul_inv_rev,schemeMap_mul,Category.assoc]

#print axioms absoluteAction
#print axioms fieldAut_x
#print axioms fieldAut_y
#print axioms pointMap_mul
end FourCorner.ThetaGaloisFieldAction
