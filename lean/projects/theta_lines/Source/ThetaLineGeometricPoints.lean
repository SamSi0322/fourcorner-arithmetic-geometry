import ThetaLineAlgebraDecomposition
import ThetaStdTotallySplit
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra
open ThetaLinesAbsoluteGalois
open scoped TensorProduct

/-- Actual algebra maps into Qbar are the prime spectrum of the real split base change. -/
def geometricHomSpecEquiv : (Associated →ₐ[ℚ] Qbar) ≃ PrimeSpectrum (Qbar ⊗[ℚ] Associated) := by
  let B := Qbar ⊗[ℚ] Associated
  haveI : Algebra.Etale Qbar B := inferInstance
  haveI : Algebra.IsFiniteSplit Qbar B := inferInstance
  exact (Algebra.TensorProduct.liftEquivRight ℚ Qbar Associated Qbar).trans
    (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum Qbar B)

instance geometricHomFintype : Fintype (Associated →ₐ[ℚ] Qbar) := by
  let B := Qbar ⊗[ℚ] Associated
  haveI : Module.Finite Qbar B := inferInstance
  haveI : IsArtinianRing B := isArtinian_of_tower Qbar inferInstance
  letI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  exact Fintype.ofEquiv (PrimeSpectrum B) geometricHomSpecEquiv.symm

theorem geometricHom_card : Fintype.card (Associated →ₐ[ℚ] Qbar) = 28 := by
  let B := Qbar ⊗[ℚ] Associated
  haveI : Module.Finite Qbar B := inferInstance
  haveI : Algebra.Etale Qbar B := inferInstance
  haveI : IsArtinianRing B := isArtinian_of_tower Qbar inferInstance
  letI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed Qbar B
  have hdim : Module.finrank Qbar B = Fintype.card (PrimeSpectrum B) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using e.toLinearEquiv.finrank_eq
  calc
    Fintype.card (Associated →ₐ[ℚ] Qbar) = Fintype.card (PrimeSpectrum B) :=
      Fintype.card_congr geometricHomSpecEquiv
    _ = Module.finrank Qbar B := hdim.symm
    _ = Module.finrank ℚ Associated := Module.finrank_baseChange
    _ = 28 := associated_degree

/-- The point map is a bijection of the ACTUAL native line locus with genuine geometric
points of the independently constructed finite étale line algebra. No individual evaluation
ring homomorphism is claimed injective. -/
def geometricPointEquiv : ActualLine ≃ (Associated →ₐ[ℚ] Qbar) :=
  Equiv.ofBijective geometricPoint ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨geometricPoint_injective, actualLine_card.trans geometricHom_card.symm⟩)

instance geometricHomAction : MulAction AbsoluteG (Associated →ₐ[ℚ] Qbar) where
  smul σ f := σ.toAlgHom.comp f
  one_smul f := by
    change (1 : AbsoluteG).toAlgHom.comp f = f
    ext x
    rfl
  mul_smul σ τ f := by
    change (σ * τ).toAlgHom.comp f = σ.toAlgHom.comp (τ.toAlgHom.comp f)
    ext x
    rfl

theorem geometricPointEquiv_absolute (σ : AbsoluteG) (P : ActualLine) :
    geometricPointEquiv (σ • P) = σ • geometricPointEquiv P := geometricPoint_absolute σ P

/-- Full LINE-algebra endpoint, retaining the actual native Galois point identification. -/
theorem associated_line_algebra :
    Module.Finite ℚ Associated ∧ Algebra.Etale ℚ Associated ∧
      Nonempty (Associated ≃ₐ[ℚ] ProductModel) ∧
      Nonempty (ActualLine ≃ (Associated →ₐ[ℚ] Qbar)) ∧
      (∀ σ : AbsoluteG, ∀ P : ActualLine,
        geometricPointEquiv (σ • P) = σ • geometricPointEquiv P) :=
  ⟨inferInstance, inferInstance, ⟨algebraDecomposition⟩, ⟨geometricPointEquiv⟩,
    geometricPointEquiv_absolute⟩
end FourCorner.ThetaLineGaloisAlgebra
