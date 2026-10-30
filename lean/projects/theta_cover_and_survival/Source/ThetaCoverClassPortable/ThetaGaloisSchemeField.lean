import ThetaCoverClassPortable.NativeFunctionFieldFunctor
import ThetaCoverClassPortable.ThetaDExactChartTransitions
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_BaseChangeGalois

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaGaloisSchemeField
open ThetaDGeometricModel ThetaLiteralModels ThetaNativeFunctionFieldMap NativeFunctionFieldFunctor
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra

abbrev Gal := K ≃ₐ[ℚ] K

def baseScheme (σ : Gal) : Spec (.of K) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

instance baseScheme_isIso (σ : Gal) : IsIso (baseScheme σ) := by
  haveI : IsIso (CommRingCat.ofHom σ.toRingHom) := by
    change IsIso σ.toRingEquiv.toCommRingCatIso.hom
    infer_instance
  change IsIso (Scheme.Spec.map (CommRingCat.ofHom σ.toRingHom).op)
  infer_instance

 theorem base_square (σ : Gal) : qb ≫ 𝟙 _=baseScheme σ ≫ qb := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫ 𝟙 _=
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
  rw [Category.comp_id,←Spec.map_comp]
  congr 1
  ext a
  exact (σ.commutes a).symm

/-- The actual basechange Scheme automorphism, not a coefficient-basis action. -/
def schemeMap (σ : Gal) : geometricD ⟶ geometricD :=
  pullback.map (dToBase ℚ) qb (dToBase ℚ) qb (𝟙 _) (baseScheme σ) (𝟙 _)
    (by simp) (base_square σ)

instance schemeMap_isIso (σ : Gal) : IsIso (schemeMap σ) := by
  dsimp [schemeMap]
  infer_instance

 theorem schemeMap_fst (σ : Gal) : schemeMap σ ≫ pullback.fst (dToBase ℚ) qb=
    pullback.fst (dToBase ℚ) qb := by simp [schemeMap,pullback.map]

 theorem schemeMap_snd (σ : Gal) : schemeMap σ ≫ toBase=toBase ≫ baseScheme σ := by
  simp [schemeMap,toBase,pullback.map]

 theorem baseScheme_mul (σ ρ : Gal) : baseScheme (σ*ρ)=baseScheme σ ≫ baseScheme ρ := by
  dsimp [baseScheme]
  rw [←Spec.map_comp]
  congr 1

 theorem schemeMap_one : schemeMap (1:Gal)=𝟙 geometricD := by
  apply pullback.hom_ext
  · simp only [schemeMap_fst,Category.id_comp]
  · rw [schemeMap_snd]
    change toBase ≫ Spec.map (𝟙 (CommRingCat.of K))=toBase
    simp

 theorem schemeMap_mul (σ ρ : Gal) : schemeMap (σ*ρ)=schemeMap σ ≫ schemeMap ρ := by
  apply pullback.hom_ext
  · rw [Category.assoc,schemeMap_fst,schemeMap_fst,schemeMap_fst]
  · change schemeMap (σ*ρ) ≫ toBase=(schemeMap σ ≫ schemeMap ρ) ≫ toBase
    rw [schemeMap_snd,Category.assoc,schemeMap_snd,←Category.assoc,schemeMap_snd,
      Category.assoc,baseScheme_mul]

/-- Ring automorphism of the SAME original native function field, induced
by the actual generic stalk map of the actual Scheme automorphism. -/
def fieldAut (σ : Gal) : field ≃+* field := fieldRingEquiv (schemeMap σ)

 theorem fieldAut_toRingHom (σ : Gal) : (fieldAut σ).toRingHom=fieldMap (schemeMap σ) := rfl

 theorem fieldAut_constants (σ : Gal) (a : K) :
    fieldAut σ (algebraMap K field a)=algebraMap K field (σ a) :=
  semilinear_base_compatibility (schemeMap σ) toBase toBase σ.toRingEquiv
    (schemeMap_snd σ) a

def semilinear (σ : Gal) : SemilinearAut K field :=
  ⟨(fieldAut σ,σ.toRingEquiv),fieldAut_constants σ⟩

#print axioms schemeMap
#print axioms schemeMap_mul
#print axioms fieldAut_constants
#print axioms semilinear
end FourCorner.ThetaGaloisSchemeField
