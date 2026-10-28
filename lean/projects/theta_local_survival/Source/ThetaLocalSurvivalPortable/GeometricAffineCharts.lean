import ThetaLocalSurvivalPortable.GeometricSchemeAction
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace FourCorner.ThetaLocalSurvival.ComponentDescent
variable {Y : Scheme} (f : Y ⟶ qqBase)
variable (A : Type) [CommRing A] [Algebra ℚ A]
abbrev chartBase : Spec (.of A) ⟶ qqBase := Spec.map (CommRingCat.ofHom (algebraMap ℚ A))
variable (j : Spec (.of A) ⟶ Y) (hj : j ≫ f=chartBase A)
abbrev chartFibre := pullback j (geometricProjection f)
abbrev chartBaseSource := pullback (chartBase A) scalarExtension

def chartBaseToGeometric : chartBaseSource A ⟶ geometricScheme f :=
  pullback.lift (pullback.fst (chartBase A) scalarExtension ≫ j)
    (pullback.snd (chartBase A) scalarExtension) (by
      rw [Category.assoc,hj]
      exact pullback.condition)

def chartFibreIso : chartFibre f A j ≅ chartBaseSource A where
  hom := pullback.lift (pullback.fst j (geometricProjection f))
    (pullback.snd j (geometricProjection f) ≫ geometricToOmega f) (by
      rw [←hj,←Category.assoc,pullback.condition,Category.assoc,pullback.condition]
      simp only [geometricToOmega,Category.assoc])
  inv := pullback.lift (pullback.fst (chartBase A) scalarExtension) (chartBaseToGeometric f A j hj) (by
    simp [chartBaseToGeometric,geometricProjection])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext
      · simpa [chartBaseToGeometric,geometricProjection,Category.assoc] using
          (pullback.condition (f:=j) (g:=geometricProjection f))
      · simp [chartBaseToGeometric,geometricToOmega,Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> simp [chartBaseToGeometric,geometricToOmega,Category.assoc]

@[reassoc (attr := simp)] theorem chartFibreIso_inv_fst :
    (chartFibreIso f A j hj).inv ≫ pullback.fst j (geometricProjection f)=
      pullback.fst (chartBase A) scalarExtension := by simp [chartFibreIso]
@[reassoc (attr := simp)] theorem chartFibreIso_inv_snd_fst :
    (chartFibreIso f A j hj).inv ≫ pullback.snd j (geometricProjection f) ≫ geometricProjection f=
      pullback.fst (chartBase A) scalarExtension ≫ j := by
  simp [chartFibreIso,chartBaseToGeometric,geometricProjection,Category.assoc]
@[reassoc (attr := simp)] theorem chartFibreIso_inv_snd_snd :
    (chartFibreIso f A j hj).inv ≫ pullback.snd j (geometricProjection f) ≫ geometricToOmega f=
      pullback.snd (chartBase A) scalarExtension := by
  simp [chartFibreIso,chartBaseToGeometric,geometricToOmega,Category.assoc]

def tensorBaseIso : Spec (.of (tensorRing Omega A)) ≅ chartBaseSource A :=
  (pullbackSpecIso ℚ Omega A).symm ≪≫ pullbackSymmetry scalarExtension (chartBase A)

@[reassoc (attr := simp)] theorem tensorBaseIso_hom_fst :
    (tensorBaseIso A).hom ≫ pullback.fst (chartBase A) scalarExtension=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom) := by
  simp only [tensorBaseIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullbackSymmetry_hom_comp_fst,pullbackSpecIso_inv_snd]
  rfl
@[reassoc (attr := simp)] theorem tensorBaseIso_hom_snd :
    (tensorBaseIso A).hom ≫ pullback.snd (chartBase A) scalarExtension=
      Spec.map (CommRingCat.ofHom (algebraMap Omega (tensorRing Omega A))) := by
  simp only [tensorBaseIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    pullbackSymmetry_hom_comp_snd,pullbackSpecIso_inv_fst]
  rfl

/-- Actual affine chart of the literal geometric base change, assembled
from actual pullback and tensor-product isomorphisms. -/
def geometricChartMap : Spec (.of (tensorRing Omega A)) ⟶ geometricScheme f :=
  (tensorBaseIso A).hom ≫ (chartFibreIso f A j hj).inv ≫ pullback.snd j (geometricProjection f)

@[reassoc (attr := simp)] theorem geometricChartMap_fst :
    geometricChartMap f A j hj ≫ geometricProjection f=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom) ≫ j := by
  simp only [geometricChartMap,Category.assoc,chartFibreIso_inv_snd_fst,tensorBaseIso_hom_fst_assoc]
@[reassoc (attr := simp)] theorem geometricChartMap_snd :
    geometricChartMap f A j hj ≫ geometricToOmega f=
      Spec.map (CommRingCat.ofHom (algebraMap Omega (tensorRing Omega A))) := by
  simp only [geometricChartMap,Category.assoc,chartFibreIso_inv_snd_snd,tensorBaseIso_hom_snd]

theorem geometricChartMap_openImmersion [IsOpenImmersion j] : IsOpenImmersion (geometricChartMap f A j hj) := by
  unfold geometricChartMap
  infer_instance

/-- The chart covers exactly the full preimage of the original affine
chart, so points over any chosen base point are all represented. -/
theorem geometricChartMap_range : Set.range (geometricChartMap f A j hj)=
    geometricProjection f ⁻¹' Set.range j := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom) t,?_⟩
    exact (congrArg (fun g : Spec (.of (tensorRing Omega A)) ⟶ Y => g t) (geometricChartMap_fst f A j hj)).symm
  · intro hx
    have hh : x∈Set.range (pullback.snd j (geometricProjection f)) := by
      rw [Scheme.Pullback.range_snd]
      exact hx
    obtain ⟨z,hz⟩ := hh
    obtain ⟨u,hu⟩ := (chartFibreIso f A j hj).inv.homeomorph.surjective z
    obtain ⟨t,ht⟩ := (tensorBaseIso A).hom.homeomorph.surjective u
    change (chartFibreIso f A j hj).inv u=z at hu
    change (tensorBaseIso A).hom t=u at ht
    refine ⟨t,?_⟩
    change pullback.snd j (geometricProjection f)
      ((chartFibreIso f A j hj).inv ((tensorBaseIso A).hom t))=x
    rw [ht,hu,hz]

end FourCorner.ThetaLocalSurvival.ComponentDescent
