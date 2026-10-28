import ThetaLocalSurvivalPortable.GaloisTensorProfinite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaLocalSurvival.ComponentDescent

abbrev qqBase := Spec (.of ℚ)
abbrev omegaBase := Spec (.of Omega)
abbrev scalarExtension : omegaBase ⟶ qqBase := Spec.map (CommRingCat.ofHom (algebraMap ℚ Omega))

variable {Y : Scheme} (f : Y ⟶ qqBase)
abbrev geometricScheme := pullback f scalarExtension
abbrev geometricProjection : geometricScheme f ⟶ Y := pullback.fst f scalarExtension
abbrev geometricToOmega : geometricScheme f ⟶ omegaBase := pullback.snd f scalarExtension

def scalarAction (σ : GaloisGroup) : omegaBase ⟶ omegaBase :=
  Spec.map (CommRingCat.ofHom σ.symm.toRingHom)

theorem scalarAction_over (σ : GaloisGroup) : scalarAction σ ≫ scalarExtension=scalarExtension := by
  unfold scalarAction scalarExtension
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact σ.symm.toAlgHom.comp_algebraMap

theorem scalarAction_inverse (σ : GaloisGroup) : scalarAction σ ≫ scalarAction σ.symm=𝟙 omegaBase := by
  change Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)=_
  rw [←Spec.map_comp]
  have h : CommRingCat.ofHom σ.toRingHom ≫ CommRingCat.ofHom σ.symm.toRingHom=𝟙 (CommRingCat.of Omega) := by
    ext x
    exact σ.symm_apply_apply x
  rw [h,Spec.map_id]

theorem scalarAction_inverse_symm (σ : GaloisGroup) : scalarAction σ.symm ≫ scalarAction σ=𝟙 omegaBase := by
  simpa only [AlgEquiv.symm_symm] using scalarAction_inverse σ.symm

def geometricAction (σ : GaloisGroup) : geometricScheme f ⟶ geometricScheme f :=
  pullback.lift (geometricProjection f) (geometricToOmega f ≫ scalarAction σ) (by
    rw [Category.assoc,scalarAction_over]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem geometricAction_fst (σ : GaloisGroup) :
    geometricAction f σ ≫ geometricProjection f=geometricProjection f := by
  simp [geometricAction,geometricProjection]
@[reassoc (attr := simp)] theorem geometricAction_snd (σ : GaloisGroup) :
    geometricAction f σ ≫ geometricToOmega f=geometricToOmega f ≫ scalarAction σ := by
  simp [geometricAction,geometricToOmega]

def geometricActionIso (σ : GaloisGroup) : geometricScheme f ≅ geometricScheme f where
  hom := geometricAction f σ
  inv := geometricAction f σ.symm
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,geometricAction_fst,Category.id_comp]
    · simp only [Category.assoc,geometricAction_snd,geometricAction_snd_assoc,
        scalarAction_inverse,scalarAction_inverse_symm,Category.comp_id,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,geometricAction_fst,Category.id_comp]
    · simp only [Category.assoc,geometricAction_snd,geometricAction_snd_assoc,
        scalarAction_inverse,scalarAction_inverse_symm,Category.comp_id,Category.id_comp]

def geometricHomeomorph (σ : GaloisGroup) : geometricScheme f ≃ₜ geometricScheme f :=
  (geometricActionIso f σ).hom.homeomorph

variable (O : qqBase ⟶ Y) (hO : O ≫ f=𝟙 qqBase)
def geometricOrigin : omegaBase ⟶ geometricScheme f :=
  pullback.lift (scalarExtension ≫ O) (𝟙 _) (by simp only [Category.assoc,hO,Category.comp_id,Category.id_comp])

theorem geometricOrigin_action (σ : GaloisGroup) :
    geometricOrigin f O hO ≫ geometricAction f σ=scalarAction σ ≫ geometricOrigin f O hO := by
  apply pullback.hom_ext
  · simp only [Category.assoc,geometricAction_fst]
    simp only [geometricOrigin,pullback.lift_fst,←Category.assoc,scalarAction_over]
  · simp only [Category.assoc,geometricAction_snd]
    simp [geometricOrigin,Category.assoc]
    exact Category.id_comp _

def geometricOriginPoint : geometricScheme f := geometricOrigin f O hO (IsLocalRing.closedPoint Omega)

theorem geometricOriginPoint_fixed (σ : GaloisGroup) :
    geometricHomeomorph f σ (geometricOriginPoint f O hO)=geometricOriginPoint f O hO := by
  have h := congrArg (fun g : omegaBase ⟶ geometricScheme f => g (IsLocalRing.closedPoint Omega))
    (geometricOrigin_action f O hO σ)
  change geometricAction f σ (geometricOrigin f O hO (IsLocalRing.closedPoint Omega))=
    geometricOrigin f O hO (scalarAction σ (IsLocalRing.closedPoint Omega)) at h
  rw [show scalarAction σ (IsLocalRing.closedPoint Omega)=IsLocalRing.closedPoint Omega from
    Subsingleton.elim (α:=PrimeSpectrum Omega) _ _] at h
  exact h

theorem scalarExtension_integral : IsIntegralHom scalarExtension := by
  rw [IsIntegralHom.SpecMap_iff]
  change (algebraMap ℚ Omega).IsIntegral
  rw [algebraMap_isIntegral_iff]
  infer_instance

theorem geometricProjection_closed : IsClosedMap (geometricProjection f) := by
  letI := scalarExtension_integral
  letI : IsIntegralHom (geometricProjection f) := inferInstance
  exact (geometricProjection f).isClosedMap

theorem geometricProjection_surjective : Function.Surjective (geometricProjection f) := by
  letI : Surjective scalarExtension := ⟨fun x => ⟨IsLocalRing.closedPoint Omega,
    Subsingleton.elim (α:=PrimeSpectrum ℚ) _ _⟩⟩
  letI : Surjective (geometricProjection f) := inferInstance
  exact (geometricProjection f).surjective

end FourCorner.ThetaLocalSurvival.ComponentDescent
