import ThetaLocalSurvivalPortable.GeometricAffineCharts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Pointwise
namespace FourCorner.ThetaLocalSurvival.ComponentDescent
variable (A : Type) [CommRing A] [Algebra ℚ A]

@[reassoc] theorem tensor_spec_toA (σ : GaloisGroup) :
    Spec.map (CommRingCat.ofHom (tensorAut Omega A σ.symm).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom)=
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom) := by
  rw [←Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change tensorAut Omega A σ.symm (1 ⊗ₜ[ℚ] a)=1 ⊗ₜ[ℚ] a
  rw [tensorAut_tmul,map_one]

@[reassoc] theorem tensor_spec_toOmega (σ : GaloisGroup) :
    Spec.map (CommRingCat.ofHom (tensorAut Omega A σ.symm).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Omega (tensorRing Omega A)))=
      Spec.map (CommRingCat.ofHom (algebraMap Omega (tensorRing Omega A))) ≫ scalarAction σ := by
  unfold scalarAction
  rw [←Spec.map_comp,←Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro l
  change tensorAut Omega A σ.symm (algebraMap Omega (tensorRing Omega A) l)=
    algebraMap Omega (tensorRing Omega A) (σ.symm l)
  rw [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.algebraMap_apply,tensorAut_tmul]
  rfl

variable {Y : Scheme} (f : Y ⟶ qqBase) (j : Spec (.of A) ⟶ Y) (hj : j ≫ f=chartBase A)

/-- Actual compatibility of the global scalar action with the actual
tensor affine chart, proved by the two genuine pullback projections. -/
theorem geometricChartMap_action (σ : GaloisGroup) :
    geometricChartMap f A j hj ≫ geometricAction f σ=
      Spec.map (CommRingCat.ofHom (tensorAut Omega A σ.symm).toRingHom) ≫ geometricChartMap f A j hj := by
  apply pullback.hom_ext
  · simp only [Category.assoc,geometricAction_fst,geometricChartMap_fst]
    rw [←Category.assoc,tensor_spec_toA]
  · simp only [Category.assoc,geometricAction_snd,geometricChartMap_snd_assoc,geometricChartMap_snd]
    exact (tensor_spec_toOmega A σ).symm

/-- The scalar scheme action is exactly the native prime-ideal Galois
action used by the proved orbit-fibre theorem. -/
theorem tensor_spec_action_ideal (σ : GaloisGroup) (P : Spec (.of (tensorRing Omega A))) :
    (Spec.map (CommRingCat.ofHom (tensorAut Omega A σ.symm).toRingHom) P).asIdeal=σ • P.asIdeal := by
  rw [Ideal.pointwise_smul_eq_comap]
  rfl

end FourCorner.ThetaLocalSurvival.ComponentDescent
