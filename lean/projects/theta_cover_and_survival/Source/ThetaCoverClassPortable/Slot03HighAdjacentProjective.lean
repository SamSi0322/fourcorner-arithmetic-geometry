import ThetaCoverClassPortable.Slot02HighGenericChart
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import ThetaCoverClassPortable.Slot03HighAdjacentGenus

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.Slot03HighAdjacentProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
abbrev Ambient (K : Type u) [CommRing K] := MvPolynomial (Fin 5) K
abbrev AffineAmbient (K : Type u) [CommRing K] := MvPolynomial (Fin 4) K
abbrev grading (K : Type u) [Field K] := homogeneousSubmodule (Fin 5) K

/-- Ordered homogeneous coordinates are U,V,P,Q,T. -/
def quadric (c : K) : Fin 3 → Ambient K
  | 0 => C (c^2 - 1) * X 0 ^ 2 + C (c^2) * X 1 ^ 2 - C (c^2*(c^2-1)) * X 4 ^ 2
  | 1 => X 2 ^ 2 - (X 0 + X 4) ^ 2 - (X 1 - C 2 * X 4) ^ 2
  | 2 => X 3 ^ 2 - (X 0 - X 4) ^ 2 - (X 1 - C 2 * X 4) ^ 2

theorem quadric_homogeneous (c : K) (i : Fin 3) : (quadric c i).IsHomogeneous 2 := by
  fin_cases i
  · exact ((isHomogeneous_C_mul_X_pow _ _ _).add
      (isHomogeneous_C_mul_X_pow _ _ _)).sub (isHomogeneous_C_mul_X_pow _ _ _)
  · exact ((isHomogeneous_X_pow _ _).sub
      (by simpa using ((isHomogeneous_X K 0).add (isHomogeneous_X K 4)).pow 2)).sub
      (by simpa using ((isHomogeneous_X K 1).sub ((isHomogeneous_X K 4).C_mul 2)).pow 2)
  · exact ((isHomogeneous_X_pow _ _).sub
      (by simpa using ((isHomogeneous_X K 0).sub (isHomogeneous_X K 4)).pow 2)).sub
      (by simpa using ((isHomogeneous_X K 1).sub ((isHomogeneous_X K 4).C_mul 2)).pow 2)

def ideal (c : K) : Ideal (Ambient K) := Ideal.span (Set.range (quadric c))

theorem ideal_homogeneous (c : K) : (ideal c).IsHomogeneous (grading K) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i,rfl⟩
  exact ⟨2, quadric_homogeneous c i⟩

def homogeneousIdeal (c : K) : HomogeneousIdeal (grading K) := ⟨ideal c, ideal_homogeneous c⟩
abbrev coordinateRing (c : K) := Ambient K ⧸ ideal c
abbrev quotientGrading (c : K) := quotGrading (grading K) (ideal c)
instance (c : K) : GradedRing (quotientGrading c) :=
  quotGradingGradedRingOfHomogeneous (grading K) (homogeneousIdeal c)

def curve (c : K) : Scheme := Proj (quotientGrading c)
def embedding (c : K) : curve c ⟶ Proj (grading K) :=
  ProjectiveQuotient.quotientMap (grading K) (homogeneousIdeal c)
theorem embedding_isClosedImmersion (c : K) : IsClosedImmersion (embedding c) :=
  ProjectiveQuotient.quotientMap_isClosedImmersion (grading K) (homogeneousIdeal c)

def spaceToBase : Proj (grading K) ⟶ Spec (.of K) :=
  Proj.toSpecZero (grading K) ≫
    Spec.map (CommRingCat.ofHom (Slot02HighProjSpace.grad0Equiv K 4).toRingHom)

def toBase (c : K) : curve c ⟶ Spec (.of K) := embedding c ≫ spaceToBase

instance ambientFiniteType : Algebra.FiniteType (grading K 0) (Ambient K) := by
  classical
  refine ⟨⟨Finset.univ.image MvPolynomial.X, eq_top_iff.mpr fun p _ => ?_⟩⟩
  induction p using MvPolynomial.induction_on with
  | C r => exact Subalgebra.algebraMap_mem _ (⟨C r,isHomogeneous_C _ r⟩ : grading K 0)
  | add p q hp hq => exact Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    exact Subalgebra.mul_mem _ (hp trivial)
      (Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ j))))

theorem spaceToBase_isProper : IsProper (spaceToBase (K := K)) := by
  unfold spaceToBase
  haveI : IsIso (CommRingCat.ofHom (Slot02HighProjSpace.grad0Equiv K 4).toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (Slot02HighProjSpace.grad0Equiv K 4).bijective
  infer_instance

theorem toBase_isProper (c : K) : IsProper (toBase c) := by
  haveI := embedding_isClosedImmersion c
  haveI := spaceToBase_isProper (K := K)
  unfold toBase
  infer_instance

def affineEquation (c : K) : Fin 3 → AffineAmbient K
  | 0 => C (c^2 - 1) * X 0 ^ 2 + C (c^2) * X 1 ^ 2 - C (c^2*(c^2-1))
  | 1 => X 2 ^ 2 - (X 0 + 1) ^ 2 - (X 1 - 2) ^ 2
  | 2 => X 3 ^ 2 - (X 0 - 1) ^ 2 - (X 1 - 2) ^ 2

abbrev affineIdeal (c : K) := Ideal.span (Set.range (affineEquation c))
abbrev affineRing (c : K) := AffineAmbient K ⧸ affineIdeal c

theorem dehomT_quadric (c : K) (i : Fin 3) :
    OppositeHomogeneousQuadrics.dehomT (quadric c i) = affineEquation c i := by
  fin_cases i <;> simp [OppositeHomogeneousQuadrics.dehomT, quadric, affineEquation, map_ofNat]

theorem dehomT_ideal (c : K) : Ideal.map OppositeHomogeneousQuadrics.dehomT (ideal c) = affineIdeal c := by
  rw [ideal, Ideal.map_span, ← Set.range_comp]
  exact congrArg (Ideal.span) (congrArg Set.range (funext (dehomT_quadric c)))

def affineOpenCover (c : K) : (curve c).AffineOpenCover :=
  ProjectiveQuotientCharts.affineOpenCover K 4 (homogeneousIdeal c)

def chartSchemeIso (c : K) :
    (Proj.basicOpen (quotientGrading c)
      (Ideal.Quotient.mk (ideal c) (MvPolynomial.X (4 : Fin 5)))).toScheme ≅
      Spec (.of (affineRing c)) := by
  have h : GenericFiveChart.affineIdeal (quadric c) = affineIdeal c := by
    apply congrArg Ideal.span
    apply congrArg Set.range
    exact funext (dehomT_quadric c)
  have e := GenericFiveChart.chartSchemeIso (quadric c) (quadric_homogeneous c)
  change (Proj.basicOpen (quotientGrading c)
    (Ideal.Quotient.mk (ideal c) (MvPolynomial.X (4 : Fin 5)))).toScheme ≅
      Spec (.of (AffineAmbient K ⧸ GenericFiveChart.affineIdeal (quadric c))) at e
  rw [h] at e
  exact e

#print axioms chartSchemeIso
#print axioms curve
#print axioms embedding_isClosedImmersion
#print axioms toBase_isProper
#print axioms dehomT_quadric
end FourCorner.Slot03HighAdjacentProjective
