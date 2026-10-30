import ThetaCoverClassPortable.Slot03AdjacentGeometric
import Mathlib.RingTheory.Localization.LocalizationLocalization

noncomputable section
open scoped TensorProduct
namespace FourCorner.Slot03High

variable (K R E L : Type*) [Field K] [CommRing R] [IsDomain R]
  [Field E] [Field L] [Algebra K R] [Algebra K E] [Algebra R E]
  [IsScalarTower K R E] [IsFractionRing R E] [Algebra K L]

abbrev tensorMap : R ⊗[K] L →ₐ[K] E ⊗[K] L :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K R E) (AlgHom.id K L)

abbrev tensorAlgebra : Algebra (R ⊗[K] L) (E ⊗[K] L) :=
  (tensorMap K R E L).toRingHom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
def tensorCancel :
    letI := tensorAlgebra K R E L
    ((R ⊗[K] L) ⊗[R] E) ≃ₐ[R ⊗[K] L] (E ⊗[K] L) := by
  letI := tensorAlgebra K R E L
  let e := (Algebra.TensorProduct.comm R (R ⊗[K] L) E).trans
    (Algebra.TensorProduct.cancelBaseChange K R R E L)
  refine { e.toRingEquiv with commutes' := ?_ }
  intro a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    change e (((x + y) ⊗ₜ[R] 1)) = _
    rw [TensorProduct.add_tmul, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul r l =>
    change e ((r ⊗ₜ[K] l) ⊗ₜ[R] 1) = tensorMap K R E L (r ⊗ₜ[K] l)
    simp [e, tensorMap, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]

theorem tensor_isLocalization :
    letI := tensorAlgebra K R E L
    IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      (E ⊗[K] L) := by
  letI := tensorAlgebra K R E L
  have : IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      ((R ⊗[K] L) ⊗[R] E) := IsLocalization.tensor E (nonZeroDivisors R)
  exact IsLocalization.isLocalization_of_algEquiv _ (tensorCancel K R E L)

end FourCorner.Slot03High

namespace FourCorner.Slot03High
variable (L A B : Type*) [Field L] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra L A] [Algebra L B] [Algebra A B] [IsScalarTower L A B]
  (S : Submonoid A) [IsLocalization S B]

set_option backward.isDefEq.respectTransparency false in
def fractionLocalizationEquiv (hS : S ≤ nonZeroDivisors A) :
    FractionRing A ≃ₐ[L] FractionRing B := by
  let f : B →ₐ[L] FractionRing A :=
    IsLocalization.liftAlgHom (f := IsScalarTower.toAlgHom L A (FractionRing A))
      (fun s => IsLocalization.map_units (FractionRing A) ⟨s.1, hS s.2⟩)
  letI : Algebra B (FractionRing A) := f.toRingHom.toAlgebra
  haveI : IsScalarTower L B (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun l => (f.commutes l).symm
  haveI : IsScalarTower A B (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      exact (IsLocalization.lift_eq
        (fun s => IsLocalization.map_units (FractionRing A) ⟨s.1, hS s.2⟩) a).symm
  haveI : IsFractionRing B (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S B (FractionRing A)
  exact IsFractionRing.algEquivOfAlgEquiv (AlgEquiv.refl : B ≃ₐ[L] B)

section TensorFraction
variable (K R E L : Type*) [Field K] [CommRing R] [IsDomain R]
  [Field E] [Field L] [Algebra K R] [Algebra K E] [Algebra R E]
  [IsScalarTower K R E] [IsFractionRing R E] [Algebra K L]
  [IsDomain (R ⊗[K] L)]

set_option backward.isDefEq.respectTransparency false in
def tensorFractionEquivRight :
    letI : Algebra L (R ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    letI : IsDomain (E ⊗[K] L) :=
      GeometricFractionField.isDomain_fractionRing_tensor K R E L
    letI : Algebra L (E ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    FractionRing (R ⊗[K] L) ≃ₐ[L] FractionRing (E ⊗[K] L) := by
  letI : Algebra L (R ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  letI : IsDomain (E ⊗[K] L) :=
    GeometricFractionField.isDomain_fractionRing_tensor K R E L
  letI : Algebra L (E ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  letI := tensorAlgebra K R E L
  haveI : IsScalarTower L (R ⊗[K] L) (E ⊗[K] L) :=
    IsScalarTower.of_algebraMap_eq fun l => by
      change (1 : E) ⊗ₜ[K] l = tensorMap K R E L ((1 : R) ⊗ₜ[K] l)
      simp [tensorMap]
  haveI := tensor_isLocalization K R E L
  have hle : Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R) ≤
      nonZeroDivisors (R ⊗[K] L) := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro hzero
    have hinj := Algebra.TensorProduct.includeLeft_injective
      (R := K) (S := K) (A := R) (B := L) (algebraMap K L).injective
    exact nonZeroDivisors.ne_zero hr (hinj (hzero.trans (map_zero _).symm))
  exact fractionLocalizationEquiv L (R ⊗[K] L) (E ⊗[K] L) _ hle

end TensorFraction

section Comm
variable (K R L : Type*) [Field K] [CommRing R] [Field L] [Algebra K R] [Algebra K L]

def tensorComm :
    letI : Algebra L (R ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
    (R ⊗[K] L) ≃ₐ[L] (L ⊗[K] R) := by
  letI : Algebra L (R ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  exact { (Algebra.TensorProduct.comm K R L).toRingEquiv with commutes' := fun _ => rfl }
end Comm

section Left
variable (K R E L : Type*) [Field K] [CommRing R] [IsDomain R]
  [Field E] [Field L] [Algebra K R] [Algebra K E] [Algebra R E]
  [IsScalarTower K R E] [IsFractionRing R E] [Algebra K L]
  [IsDomain (L ⊗[K] R)]

set_option backward.isDefEq.respectTransparency false in
def tensorFractionEquiv :
    letI : IsDomain (L ⊗[K] E) :=
      GeometricFractionField.isDomain_baseChange_fractionRing K R E L
    FractionRing (L ⊗[K] R) ≃ₐ[L] FractionRing (L ⊗[K] E) := by
  haveI : IsDomain (R ⊗[K] L) :=
    Function.Injective.isDomain (Algebra.TensorProduct.comm K R L).toRingEquiv
      (Algebra.TensorProduct.comm K R L).injective
  haveI : IsDomain (E ⊗[K] L) :=
    GeometricFractionField.isDomain_fractionRing_tensor K R E L
  letI : IsDomain (L ⊗[K] E) :=
    GeometricFractionField.isDomain_baseChange_fractionRing K R E L
  letI : Algebra L (R ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (E ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  let eR : FractionRing (R ⊗[K] L) ≃ₐ[L] FractionRing (L ⊗[K] R) :=
    IsFractionRing.algEquivOfAlgEquiv (tensorComm K R L)
  let eE : FractionRing (E ⊗[K] L) ≃ₐ[L] FractionRing (L ⊗[K] E) :=
    IsFractionRing.algEquivOfAlgEquiv (tensorComm K E L)
  exact eR.symm.trans ((tensorFractionEquivRight K R E L).trans eE)
end Left

#print axioms tensor_isLocalization
#print axioms fractionLocalizationEquiv
#print axioms tensorFractionEquivRight
#print axioms tensorFractionEquiv
end FourCorner.Slot03High
