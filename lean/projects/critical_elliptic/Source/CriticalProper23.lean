import CriticalProj23
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! The literal critical intersection as a proper scheme over the original field. -/
noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalProj23
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k]

def ambientDegreeZeroEquiv : k ≃+* homogeneousSubmodule (Fin 4) k 0 where
  toFun r := ⟨C r, isHomogeneous_C _ r⟩
  invFun p := constantCoeff p.1
  left_inv r := by simp
  right_inv p := by
    ext : 1
    have hp : p.1.IsHomogeneous 0 := p.2
    ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [constantCoeff]
    · rw [coeff_C, if_neg (Ne.symm hd)]
      by_contra h
      refine hd (Finsupp.ext fun j => ?_)
      have hdeg : Finsupp.weight (1 : Fin 4 → ℕ) d = 0 := hp (fun h0 => h h0.symm)
      simp only [Finsupp.weight_apply,Pi.one_apply,smul_eq_mul,mul_one,Finsupp.sum] at hdeg
      by_cases hj : j ∈ d.support
      · exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hdeg j hj
      · exact Finsupp.notMem_support_iff.mp hj
  map_mul' a b := by ext : 1; simp
  map_add' a b := by ext : 1; simp

def ambientToSpec : Proj (homogeneousSubmodule (Fin 4) k) ⟶ Spec (.of k) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom ambientDegreeZeroEquiv.toRingHom)

instance ambientFiniteType :
    Algebra.FiniteType (homogeneousSubmodule (Fin 4) k 0) (Ambient k) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (⟨C r,isHomogeneous_C _ r⟩ : homogeneousSubmodule (Fin 4) k 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

theorem ambientToSpec_isProper : IsProper (ambientToSpec (k:=k)) := by
  unfold ambientToSpec
  haveI : IsProper (Proj.toSpecZero (homogeneousSubmodule (Fin 4) k)) := inferInstance
  haveI : IsIso (CommRingCat.ofHom (ambientDegreeZeroEquiv (k:=k)).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ambientDegreeZeroEquiv.bijective
  haveI : IsIso (Spec.map (CommRingCat.ofHom (ambientDegreeZeroEquiv (k:=k)).toRingHom)) := inferInstance
  infer_instance

/-- Structural morphism of the actual critical scheme to its original field. -/
def criticalToSpec (i : k) : criticalCurve i ⟶ Spec (.of k) := inclusion i ≫ ambientToSpec

theorem criticalToSpec_isProper (i : k) : IsProper (criticalToSpec i) := by
  haveI : IsClosedImmersion (inclusion i) := inclusion_isClosedImmersion i
  haveI : IsProper (ambientToSpec (k:=k)) := ambientToSpec_isProper
  unfold criticalToSpec
  infer_instance

#print axioms ambientToSpec_isProper
#print axioms criticalToSpec_isProper
end FourCorner.CriticalProj23
