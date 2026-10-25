import Slot03HighPullbackField
import Slot02GeometricAffineGenus
import geometry.OppositeSchemeGeometricIntegral

noncomputable section
namespace FourCorner.OppositeProjective.HighGenus
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
open OppositeSchemeModel OppositeCoordinateAlgebra OppositePolynomials

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

abbrev modelCover {K : Type} [Field K] [CharZero K] (mu nu : K) :
    (model mu nu).C.TwoAffineOpenCover :=
  SchemeModelFiniteExtension.twoAffineOpenCover K (functionField mu nu)

instance cover0Nonempty {K : Type} [Field K] [CharZero K] (mu nu : K) : Nonempty (modelCover mu nu).U0 :=
  SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0 K (functionField mu nu)
instance cover1Nonempty {K : Type} [Field K] [CharZero K] (mu nu : K) : Nonempty (modelCover mu nu).U1 :=
  SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1 K (functionField mu nu)
instance cover01Nonempty {K : Type} [Field K] [CharZero K] (mu nu : K) :
    Nonempty ((modelCover mu nu).U0 ⊓ (modelCover mu nu).U1 : (model mu nu).C.Opens) :=
  SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap K (functionField mu nu)

def tensorLiteralFractionEquiv (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu / nu) (hl : mu / nu < 2) (L : Type) [Field L] [Algebra ℚ L] :
    letI := OppositeAffineModel.rational_all_field_extensions_integral L mu nu hn hp hl
    letI := OppositeAffineModel.rational_functionField_all_extensions_domain L mu nu hn hp hl
    FractionRing (L ⊗[ℚ] ring mu nu) ≃ₐ[L]
      FractionRing (L ⊗[ℚ] functionField mu nu) := by
  letI := OppositeAffineModel.rational_coordinateRing_isDomain mu nu hn hp hl
  letI := OppositeAffineModel.rational_coordinateRing_isFractionRing mu nu hn hp hl
  letI := OppositeAffineModel.rational_all_field_extensions_integral L mu nu hn hp hl
  letI := OppositeAffineModel.rational_functionField_all_extensions_domain L mu nu hn hp hl
  exact Slot03High.tensorFractionEquiv ℚ (ring mu nu) (functionField mu nu) L

def tensorLiteralFractionEquivForAlgebra (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu / nu) (hl : mu / nu < 2) (L : Type) [Field L] [Algebra ℚ L]
    (a : Algebra ℚ (functionField mu nu)) :
    letI := a
    letI := OppositeAffineModel.rational_all_field_extensions_integral L mu nu hn hp hl
    letI := rational_tensor_domain_for_algebra L mu nu hn hp hl a
    FractionRing (L ⊗[ℚ] ring mu nu) ≃ₐ[L]
      FractionRing (L ⊗[ℚ] functionField mu nu) := by
  have ha : a = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst a
  exact tensorLiteralFractionEquiv mu nu hn hp hl L

abbrev geometricScheme (mu nu : ℚ) :=
  pullback (modelToBase mu nu) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))
abbrev geometricToBase (mu nu : ℚ) :=
  pullback.snd (modelToBase mu nu) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))

theorem geometricIntegral (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu / nu) (hl : mu / nu < 2) :
    IsIntegral (geometricScheme mu nu) := by
  letI := modelFieldAlgebra mu nu
  haveI := rational_tensor_domain_for_algebra (AlgebraicClosure ℚ) mu nu hn hp hl
    (modelFieldAlgebra mu nu)
  exact SchemeModelGeometricIntegral.isIntegral_pullback (model mu nu)
    (modelCover mu nu) (AlgebraicClosure ℚ)

def geometricLiteralFunctionFieldEquiv (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu / nu) (hl : mu / nu < 2) :
    letI := geometricIntegral mu nu hn hp hl
    letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
    letI := OppositeAffineModel.rational_all_field_extensions_integral (AlgebraicClosure ℚ) mu nu hn hp hl
    FractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] ring mu nu) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme mu nu).functionField := by
  letI := geometricIntegral mu nu hn hp hl
  letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
  letI := OppositeAffineModel.rational_all_field_extensions_integral (AlgebraicClosure ℚ) mu nu hn hp hl
  letI := modelFieldAlgebra mu nu
  haveI := rational_tensor_domain_for_algebra (AlgebraicClosure ℚ) mu nu hn hp hl
    (modelFieldAlgebra mu nu)
  exact (tensorLiteralFractionEquivForAlgebra mu nu hn hp hl (AlgebraicClosure ℚ)
      (modelFieldAlgebra mu nu)).trans
    (Slot03High.pullbackFunctionFieldEquiv (model mu nu)
      (modelCover mu nu) (AlgebraicClosure ℚ))

theorem geometric_genus_five (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu / nu) (hl : mu / nu < 2) :
    letI := geometricIntegral mu nu hn hp hl
    letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme mu nu).functionField = 5 := by
  letI := geometricIntegral mu nu hn hp hl
  letI := (baseToFunctionField (geometricToBase mu nu)).toAlgebra
  letI := OppositeAffineModel.rational_all_field_extensions_integral (AlgebraicClosure ℚ) mu nu hn hp hl
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  exact (genusFF_eq_of_algEquiv (geometricLiteralFunctionFieldEquiv mu nu hn hp hl)).symm.trans
    (OppositeGeometricAffine.tensor_fraction_genus (L := AlgebraicClosure ℚ) hm hn
      (rational_A_ne_zero mu nu hn) (rational_B_ne_zero mu nu hn hp hl) (rational_S_ne_zero mu nu hn))

#print axioms tensorLiteralFractionEquiv
#print axioms geometricLiteralFunctionFieldEquiv
#print axioms geometric_genus_five
end FourCorner.OppositeProjective.HighGenus
