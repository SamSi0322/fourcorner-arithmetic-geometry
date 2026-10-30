import ThetaCoverClassPortable.ThetaSourcePairData
import ThetaCoverClassPortable.ThetaPairDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
noncomputable section
namespace FourCorner.ThetaChartFiniteEtale
open Algebra AlgebraicGeometry
open scoped TensorProduct
open ThetaQuotientCharts ThetaChartAlgebras
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma two_unit (R : Type*) [CommRing R] [Algebra ℚ R] : IsUnit (2:R) := by
  have h:=congrArg (algebraMap ℚ R) (show (2:ℚ)*(1/2)=1 by norm_num)
  simp only [map_mul,map_ofNat,map_one] at h
  exact IsUnit.of_mul_eq_one _ h
/-- Finite and etale, derived on all three literal quartic/source chart algebras. -/
theorem chart_finite_etale (j : Fin 3) : (baseMap j).toRingHom.Finite ∧ (baseMap j).toRingHom.Etale :=
  ThetaPairDescent.finite_etale (ThetaSourcePairData.data j)
    (algebraMap ℚ (R j) (lambda j)) (base_unit_ideal j) (two_unit (R j))
lemma spec_finite (j : Fin 3) : IsFinite (Spec.map (CommRingCat.ofHom (baseMap j).toRingHom)) :=
  (IsFinite.SpecMap_iff _).mpr (chart_finite_etale j).1
lemma spec_etale (j : Fin 3) : Etale (Spec.map (CommRingCat.ofHom (baseMap j).toRingHom)) :=
  (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr (chart_finite_etale j).2
abbrev BBase (j : Fin 3) := Localization.Away (b j)
abbrev ABase (j : Fin 3) := Localization.Away (a j)
/-- Exact unit-quadratic comparison above D(B), retaining the original source algebra. -/
def quadratic_t_iso (j : Fin 3) : BBase j ⊗[R j] S j ≃ₐ[BBase j]
    ThetaQuadraticKernel.Q (algebraMap (R j) (BBase j) (b j)) :=
  ThetaPairPresentation.equiv
    (ThetaPairBaseChange.data (W:=BBase j) (ThetaSourcePairData.data j))
    (IsLocalization.Away.algebraMap_isUnit (b j))
/-- Exact unit-quadratic comparison above D(A), retaining the original source algebra. -/
def quadratic_u_iso (j : Fin 3) : ABase j ⊗[R j] S j ≃ₐ[ABase j]
    ThetaQuadraticKernel.Q (algebraMap (R j) (ABase j) (a j)) :=
  ThetaPairPresentation.equiv
    (ThetaPairBaseChange.data (W:=ABase j) (ThetaPairDescent.swap (ThetaSourcePairData.data j)))
    (IsLocalization.Away.algebraMap_isUnit (a j))
end FourCorner.ThetaChartFiniteEtale
#print axioms FourCorner.ThetaChartFiniteEtale.chart_finite_etale
#print axioms FourCorner.ThetaChartFiniteEtale.spec_finite
#print axioms FourCorner.ThetaChartFiniteEtale.spec_etale
#print axioms FourCorner.ThetaChartFiniteEtale.quadratic_t_iso
#print axioms FourCorner.ThetaChartFiniteEtale.quadratic_u_iso
