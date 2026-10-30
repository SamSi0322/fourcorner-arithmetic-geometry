import Slot03HighPullbackField
import Slot03AdjacentTensorGenus

noncomputable section
namespace FourCorner.Slot03HighAdjacent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
open FourCorner.Slot03Adjacent

def tensorLiteralFractionEquiv (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1)
    (L : Type) [Field L] [Algebra ℚ L] :
    letI := tensor_domain c hc h1 L
    letI := field_tensor_domain c hc h1 L
    FractionRing (L ⊗[ℚ] AdjacentCoordinateAlgebra.CoordinateRing c) ≃ₐ[L]
      FractionRing (L ⊗[ℚ] AdjacentGenus.field c) := by
  let h := AdjacentPolynomials.rational_admissible (K := ℚ) c hc h1
  letI := AdjacentCoordinateAlgebra.coordinateRing_isDomain c h
  letI := tensor_domain c hc h1 L
  letI := field_tensor_domain c hc h1 L
  letI : IsDomain (L ⊗[ℚ] FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c)) :=
    GeometricFractionField.isDomain_baseChange_fractionRing ℚ
      (AdjacentCoordinateAlgebra.CoordinateRing c)
      (FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c)) L
  let eF : FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c) ≃ₐ[ℚ]
      AdjacentGenus.field c := (literalFieldRingEquiv c (ne_of_gt hc) h).toRatAlgEquiv
  let eT : (L ⊗[ℚ] FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c)) ≃ₐ[L]
      (L ⊗[ℚ] AdjacentGenus.field c) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) eF
  exact (Slot03High.tensorFractionEquiv ℚ (AdjacentCoordinateAlgebra.CoordinateRing c)
    (FractionRing (AdjacentCoordinateAlgebra.CoordinateRing c)) L).trans
      (IsFractionRing.algEquivOfAlgEquiv eT)

def tensorLiteralFractionEquivForAlgebra (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1)
    (L : Type) [Field L] [Algebra ℚ L] (a : Algebra ℚ (adjacentField c)) :
    letI := a
    letI := tensor_domain c hc h1 L
    letI := tensor_domain_for_algebra L c hc h1 a
    FractionRing (L ⊗[ℚ] AdjacentCoordinateAlgebra.CoordinateRing c) ≃ₐ[L]
      FractionRing (L ⊗[ℚ] adjacentField c) := by
  have ha : a = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst a
  exact tensorLiteralFractionEquiv c hc h1 L

universe u

theorem adjacentPullbackIntegral {K : Type u} [Field K] [CharZero K]
    (c : K) (L : Type u) [Field L] [Algebra K L]
    (h : letI := modelFieldAlgebra c; IsDomain (L ⊗[K] adjacentField c)) :
    IsIntegral (pullback (modelToBase c) (Scheme.TwoAffineOpenCover.specMap K L)) := by
  letI := modelFieldAlgebra c
  haveI := h
  let V := SchemeModelFiniteExtension.twoAffineOpenCover K (adjacentField c)
  have h0 : Nonempty V.U0 := SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0 K (adjacentField c)
  have h1 : Nonempty V.U1 := SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1 K (adjacentField c)
  have h01 : Nonempty (V.U0 ⊓ V.U1 : (model c).C.Opens) :=
    SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap K (adjacentField c)
  exact @SchemeModelGeometricIntegral.isIntegral_pullback K (adjacentField c) _ _ _
    (model c) V h0 h1 h01 L _ _ h

def adjacentPullbackFieldEquiv {K : Type u} [Field K] [CharZero K]
    (c : K) (L : Type u) [Field L] [Algebra K L]
    (h : letI := modelFieldAlgebra c; IsDomain (L ⊗[K] adjacentField c)) :
    letI := modelFieldAlgebra c
    letI := adjacentPullbackIntegral c L h
    letI := (baseToFunctionField
      (pullback.snd (modelToBase c) (Scheme.TwoAffineOpenCover.specMap K L))).toAlgebra
    FractionRing (L ⊗[K] adjacentField c) ≃ₐ[L]
      (pullback (modelToBase c) (Scheme.TwoAffineOpenCover.specMap K L)).functionField := by
  letI := modelFieldAlgebra c
  haveI := h
  let V := SchemeModelFiniteExtension.twoAffineOpenCover K (adjacentField c)
  have h0 : Nonempty V.U0 := SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0 K (adjacentField c)
  have h1 : Nonempty V.U1 := SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1 K (adjacentField c)
  have h01 : Nonempty (V.U0 ⊓ V.U1 : (model c).C.Opens) :=
    SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap K (adjacentField c)
  exact @Slot03High.pullbackFunctionFieldEquiv K (adjacentField c) _ _ _
    (model c) V h0 h1 h01 L _ _ h

abbrev geometricScheme (c : ℚ) :=
  pullback (modelToBase c) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))
abbrev geometricToBase (c : ℚ) :=
  pullback.snd (modelToBase c) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))

theorem geometricIntegral (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    IsIntegral (geometricScheme c) := by
  letI := modelFieldAlgebra c
  haveI := tensor_domain_for_algebra (AlgebraicClosure ℚ) c hc h1 (modelFieldAlgebra c)
  exact adjacentPullbackIntegral c (AlgebraicClosure ℚ)
    (tensor_domain_for_algebra (AlgebraicClosure ℚ) c hc h1 (modelFieldAlgebra c))

def geometricLiteralFunctionFieldEquiv (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    letI := geometricIntegral c hc h1
    letI := (baseToFunctionField (geometricToBase c)).toAlgebra
    letI := tensor_domain c hc h1 (AlgebraicClosure ℚ)
    FractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] AdjacentCoordinateAlgebra.CoordinateRing c) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme c).functionField := by
  letI := geometricIntegral c hc h1
  letI := (baseToFunctionField (geometricToBase c)).toAlgebra
  letI := tensor_domain c hc h1 (AlgebraicClosure ℚ)
  letI := modelFieldAlgebra c
  haveI := tensor_domain_for_algebra (AlgebraicClosure ℚ) c hc h1 (modelFieldAlgebra c)
  exact (tensorLiteralFractionEquivForAlgebra c hc h1 (AlgebraicClosure ℚ) (modelFieldAlgebra c)).trans
    (adjacentPullbackFieldEquiv c (AlgebraicClosure ℚ)
      (tensor_domain_for_algebra (AlgebraicClosure ℚ) c hc h1 (modelFieldAlgebra c)))

theorem geometric_genus_five (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    letI := geometricIntegral c hc h1
    letI := (baseToFunctionField (geometricToBase c)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme c).functionField = 5 := by
  letI := geometricIntegral c hc h1
  letI := (baseToFunctionField (geometricToBase c)).toAlgebra
  letI := tensor_domain c hc h1 (AlgebraicClosure ℚ)
  exact (genusFF_eq_of_algEquiv (geometricLiteralFunctionFieldEquiv c hc h1)).symm.trans
    (rational_tensor_fraction_genus c hc h1)

#print axioms tensorLiteralFractionEquiv
#print axioms geometricLiteralFunctionFieldEquiv
#print axioms geometric_genus_five
end FourCorner.Slot03HighAdjacent

namespace FourCorner.Slot03HighAdjacent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open FourCorner.Slot03Adjacent

theorem geometric_proper (c : ℚ) : IsProper (geometricToBase c) := by
  haveI : IsProper (modelToBase c) := inferInstance
  change IsProper (pullback.snd (modelToBase c) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ)))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem geometric_smooth (c : ℚ) : SmoothOfRelativeDimension 1 (geometricToBase c) := by
  haveI : SmoothOfRelativeDimension 1 (modelToBase c) := inferInstance
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  change SmoothOfRelativeDimension 1 (pullback.snd (modelToBase c) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ)))
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

universe v
abbrev geometricCover {K : Type v} [Field K] [CharZero K] (c : K) (L : Type v)
    [Field L] [Algebra K L] :=
  (SchemeModelFiniteExtension.twoAffineOpenCover K (adjacentField c)).pullback (modelToBase c) L

theorem geometric_globalDifferentials_five (c : ℚ) (hc : 0 < c) (h1 : c ≠ 1) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (geometricToBase c) (geometricToBase c).kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ((geometricToBase c).kaehler, ⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ((geometricToBase c).kaehler, ⊤) = 5 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (geometricToBase c) (geometricToBase c).kaehler ⊤
  letI := geometricIntegral c hc h1
  letI := geometric_proper c
  letI := geometric_smooth c
  letI := (baseToFunctionField (geometricToBase c)).toAlgebra
  obtain ⟨hfin, hrk⟩ := @KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF
    (AlgebraicClosure ℚ) _ _ (geometricScheme c) (geometricCover c (AlgebraicClosure ℚ))
    (geometricToBase c) (geometricIntegral c hc h1) (geometric_proper c) (geometric_smooth c)
  exact ⟨hfin, hrk.trans (geometric_genus_five c hc h1)⟩

#print axioms geometric_proper
#print axioms geometric_smooth
#print axioms geometric_globalDifferentials_five
end FourCorner.Slot03HighAdjacent
