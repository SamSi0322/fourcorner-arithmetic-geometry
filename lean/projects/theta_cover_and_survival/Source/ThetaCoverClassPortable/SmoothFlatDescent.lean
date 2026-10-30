/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
open TensorProduct
namespace Algebra
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
lemma Smooth.of_smooth_tensorProduct_of_faithfullyFlat [Smooth T (T ⊗[R] S)] :
    Smooth R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [formallySmooth_iff]
  constructor
  · let _ : Algebra T (S ⊗[R] T) := TensorProduct.rightAlgebra
    let e : S ⊗[R] T ≃ₐ[T] T ⊗[R] S :=
      .ofRingEquiv (f := TensorProduct.comm R S T) <| by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth T (S ⊗[R] T) := .of_equiv e.symm
    let e' : (S ⊗[R] T) ⊗[S] Ω[S⁄R] ≃ₗ[S ⊗[R] T] Ω[S ⊗[R] T⁄T] :=
      KaehlerDifferential.tensorKaehlerEquiv R T S (S ⊗[R] T)
    have : Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] Ω[S⁄R]) := .of_linearEquiv e'
    have : Module.Flat S Ω[S⁄R] := Module.Flat.of_flat_tensorProduct _ _ (S ⊗[R] T)
    exact Module.Flat.projective_of_finitePresentation
  · have : Subsingleton (T ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R T (H1Cotangent R S)

end Algebra
namespace RingHom
lemma Smooth.codescendsAlong_faithfullyFlat : CodescendsAlong Smooth FaithfullyFlat := by
  refine .mk _ Smooth.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [smooth_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_smooth_tensorProduct_of_faithfullyFlat S

end RingHom
namespace FourCorner.FiniteEtalePropertyDescent
open CategoryTheory MorphismProperty AlgebraicGeometry
theorem smooth_descendsAlong :
    DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Smooth.codescendsAlong_faithfullyFlat
end FourCorner.FiniteEtalePropertyDescent
