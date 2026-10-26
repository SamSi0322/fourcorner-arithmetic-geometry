import IdealTensorDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FourCorner.IdealFlatDescent
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

/-- The actual global-section algebra of a flat surjective affine Scheme
map is faithfully flat. This is the native class installed in the caller. -/
theorem affine_global_sections_faithfully_flat (π : X ⟶ Y) [Flat π] [Surjective π] :
    letI := π.appTop.hom.toAlgebra
    Module.FaithfullyFlat Γ(Y,⊤) Γ(X,⊤) := by
  letI := π.appTop.hom.toAlgebra
  haveI : Module.Flat Γ(Y,⊤) Γ(X,⊤) := Scheme.Hom.flat_appTop π
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  have hsurj : Surjective (Spec.map π.appTop) := by
    have h : Spec.map π.appTop = X.isoSpec.inv ≫ π ≫ Y.isoSpec.hom := by
      rw [← Scheme.isoSpec_hom_naturality,Iso.inv_hom_id_assoc]
    rw [h]
    infer_instance
  exact hsurj.surj

/-- Actual affine Scheme application, with the SAME native appTop ring
homomorphism both in contraction/extension and in the tensor algebra.
For the universal divisor caller, X=C×_S X and Y=C×_S Y, and I is IB. -/
theorem affine_ideal_descends (π : X ⟶ Y) [Flat π] [Surjective π]
    (I : Ideal Γ(X,⊤))
    (hI : letI := π.appTop.hom.toAlgebra
      I.map (Algebra.TensorProduct.includeLeftRingHom :
        Γ(X,⊤) →+* Γ(X,⊤) ⊗[Γ(Y,⊤)] Γ(X,⊤)) =
      I.map (Algebra.TensorProduct.includeRight :
        Γ(X,⊤) →ₐ[Γ(Y,⊤)] Γ(X,⊤) ⊗[Γ(Y,⊤)] Γ(X,⊤)).toRingHom) :
    (I.comap π.appTop.hom).map π.appTop.hom=I := by
  letI := π.appTop.hom.toAlgebra
  letI := affine_global_sections_faithfully_flat π
  exact Ideal.map_comap_eq_self_of_map_includeLeft_eq_map_includeRight I hI

end FourCorner.IdealFlatDescent
#print axioms FourCorner.IdealFlatDescent.affine_global_sections_faithfully_flat
#print axioms FourCorner.IdealFlatDescent.affine_ideal_descends
