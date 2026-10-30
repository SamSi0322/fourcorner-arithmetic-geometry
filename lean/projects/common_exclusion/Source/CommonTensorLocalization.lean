import geometry.GeometricFractionField
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CommonTensorLocalization
open scoped TensorProduct

/-- Injectivity on polynomial tensors implies injectivity on rational-function
tensors, by the actual localization base-change equivalence. -/
theorem map_injective_of_base_injective
    (K R F L G : Type*) [Field K] [CommRing R] [Field F] [Field L] [CommRing G]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [IsFractionRing R F] [Algebra K L]
    (μ : L ⊗[K] F →+* G)
    (hμ : Function.Injective (μ.comp
      (Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K R F)).toRingHom)) :
    Function.Injective μ := by
  let B := R ⊗[K] L
  let T := B ⊗[R] F
  let e : L ⊗[K] F ≃+* T :=
    (Algebra.TensorProduct.comm K L F).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange K R F F L).symm.toRingEquiv.trans
        (Algebra.TensorProduct.comm R F B).toRingEquiv)
  let ν : T →+* G := μ.comp e.symm.toRingHom
  let S := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  have hloc : IsLocalization S T := IsLocalization.tensor F (nonZeroDivisors R)
  letI := hloc
  have hνbase : Function.Injective (ν.comp (algebraMap B T)) := by
    have heq : ν.comp (algebraMap B T) =
        (μ.comp (Algebra.TensorProduct.map (AlgHom.id K L)
          (IsScalarTower.toAlgHom K R F)).toRingHom).comp
            (Algebra.TensorProduct.comm K R L).toRingHom := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r l =>
          change μ (e.symm ((r ⊗ₜ[K] l) ⊗ₜ[R] (1:F))) = _
          have hi : e.symm ((r ⊗ₜ[K] l) ⊗ₜ[R] (1:F)) =
              l ⊗ₜ[K] algebraMap R F r := by
            change (Algebra.TensorProduct.comm K L F).symm
              ((Algebra.TensorProduct.cancelBaseChange K R F F L)
                ((Algebra.TensorProduct.comm R F B).symm
                  ((r ⊗ₜ[K] l) ⊗ₜ[R] (1:F)))) = _
            have hc : (Algebra.TensorProduct.comm R F B).symm
                ((r ⊗ₜ[K] l) ⊗ₜ[R] (1:F)) = (1:F) ⊗ₜ[R] (r ⊗ₜ[K] l) := rfl
            rw [hc,Algebra.TensorProduct.cancelBaseChange_tmul]
            rw [Algebra.smul_def,mul_one]
            rfl
          rw [hi]
          rfl
      | add x y hx hy => simpa only [map_add,hx,hy]

    rw [heq]
    exact hμ.comp (Algebra.TensorProduct.comm K R L).injective
  have hν : Function.Injective ν := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq S ν).mpr
    intro x y
    constructor
    · exact congrArg ν
    · intro hh
      exact congrArg (algebraMap B T) (hνbase hh)
  intro x y hxy
  apply e.injective
  apply hν
  change μ (e.symm (e x)) = μ (e.symm (e y))
  simpa only [e.symm_apply_apply] using hxy

#print axioms map_injective_of_base_injective
end FourCorner.CommonTensorLocalization
