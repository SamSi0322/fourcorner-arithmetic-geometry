import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Geometric integrality passes to a fraction field

The scalar extension of a fraction field is obtained by localizing the scalar
extension of its coordinate domain. The denominators remain nonzero because the
coordinate domain embeds into its tensor product with a field extension.

The localization argument follows the generic helper in the pinned upstream
`S_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_charZero`,
lines 59–81. The public interface below uses left scalar extension, as required
by geometric integrality. No characteristic or algebraic-closure hypothesis is
needed.
-/

noncomputable section

namespace FourCorner.GeometricFractionField

open scoped TensorProduct

/-- Localization preserves the domain property after extension of scalars.
This version places the extension field on the right of the tensor product. -/
theorem isDomain_fractionRing_tensor (K R F L : Type*)
    [Field K] [CommRing R] [IsDomain R] [Field F] [Field L]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [IsFractionRing R F] [Algebra K L] [IsDomain (R ⊗[K] L)] :
    IsDomain (F ⊗[K] L) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      ((R ⊗[K] L) ⊗[R] F) := IsLocalization.tensor F (nonZeroDivisors R)
  have hinj : Function.Injective (algebraMap R (R ⊗[K] L)) := by
    have h := Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := R) (B := L)
      (algebraMap K L).injective
    intro x y hxy
    exact h hxy
  have hle : Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R) ≤
      nonZeroDivisors (R ⊗[K] L) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero hx
    exact hx0 (hinj (h0.trans (map_zero _).symm))
  have : IsDomain ((R ⊗[K] L) ⊗[R] F) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors ((R ⊗[K] L) ⊗[R] F) hle
  let e : F ⊗[K] L ≃+* (R ⊗[K] L) ⊗[R] F :=
    (Algebra.TensorProduct.cancelBaseChange K R F F L).symm.toRingEquiv.trans
      (Algebra.TensorProduct.comm R F (R ⊗[K] L)).toRingEquiv
  exact Function.Injective.isDomain e e.injective

/-- If a coordinate domain stays integral over a field extension, its actual
fraction field stays integral over that same field extension. -/
theorem isDomain_baseChange_fractionRing (K R F L : Type*)
    [Field K] [CommRing R] [IsDomain R] [Field F] [Field L]
    [Algebra K R] [Algebra K F] [Algebra R F] [IsScalarTower K R F]
    [IsFractionRing R F] [Algebra K L] [IsDomain (L ⊗[K] R)] :
    IsDomain (L ⊗[K] F) := by
  have : IsDomain (R ⊗[K] L) :=
    Function.Injective.isDomain (Algebra.TensorProduct.comm K R L).toRingEquiv
      (Algebra.TensorProduct.comm K R L).injective
  have : IsDomain (F ⊗[K] L) := isDomain_fractionRing_tensor K R F L
  exact Function.Injective.isDomain (Algebra.TensorProduct.comm K L F).toRingEquiv
    (Algebra.TensorProduct.comm K L F).injective

end FourCorner.GeometricFractionField

#print axioms FourCorner.GeometricFractionField.isDomain_fractionRing_tensor
#print axioms FourCorner.GeometricFractionField.isDomain_baseChange_fractionRing
