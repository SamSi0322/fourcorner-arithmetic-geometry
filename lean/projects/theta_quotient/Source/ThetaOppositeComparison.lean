import ThetaLiteralModels
import ThetaPolynomialFunext
import OppositeProjectiveGenusFive
noncomputable section
namespace FourCorner.ThetaOppositeComparison
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousIdealQuotientGrading
open ThetaLiteralModels
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type*} [Field k] [CharZero k]
abbrev ambient := MvPolynomial (Fin 5) k
abbrev ambientGrading := homogeneousSubmodule (Fin 5) k
abbrev sIdeal := ThetaProjectiveModel.ideal (sourceEquation k) (source_homogeneous k)
abbrev oIdeal := OppositeHomogeneousQuadrics.homogeneousIdeal (1:k) 5

def scale (a : k) : ambientGrading (k:=k) →+*ᵍ ambientGrading (k:=k) where
  __ := eval₂Hom C (fun j=> if j=3 then C a*X j else X j)
  map_mem {i} {p} hp := by
    have hg (j : Fin 5) : (if j=3 then C a*X j else X j : ambient (k:=k)).IsHomogeneous 1 := by
      split_ifs
      · exact (isHomogeneous_X _ _).C_mul _
      · exact isHomogeneous_X _ _
    have h := hp.eval₂ C (fun j=>if j=3 then C a*X j else X j) (fun c=>isHomogeneous_C _ c) hg
    change (eval₂ C (fun j=>if j=3 then C a*X j else X j) p).IsHomogeneous i
    simpa only [one_mul] using h
@[simp] lemma scale_X (a : k) (j : Fin 5) : scale a (X j)=if j=3 then C a*X j else X j := by
  exact MvPolynomial.eval₂_X _ _ _
@[simp] lemma scale_C (a b : k) : scale a (C b)=C b := by exact MvPolynomial.eval₂_C _ _ _

lemma forward_equation (i : Fin 3) : scale (7:k) (OppositeHomogeneousQuadrics.quadric (1:k) 5 i) =
    ![-49*sourceEquation k 0,sourceEquation k 1-sourceEquation k 0,sourceEquation k 2-sourceEquation k 0] i := by
  fin_cases i
  all_goals simp [OppositeHomogeneousQuadrics.quadric,OppositeHomogeneousQuadrics.F0,
    OppositeHomogeneousQuadrics.F1,OppositeHomogeneousQuadrics.F2,OppositePolynomials.A,
    sourceEquation,scale, map_ofNat]
  all_goals ring
lemma backward_equation (i : Fin 3) : scale (7⁻¹:k) (sourceEquation k i) =
    ![-(49:k)⁻¹ • OppositeHomogeneousQuadrics.quadric (1:k) 5 0,
      OppositeHomogeneousQuadrics.quadric (1:k) 5 1-(49:k)⁻¹ • OppositeHomogeneousQuadrics.quadric (1:k) 5 0,
      OppositeHomogeneousQuadrics.quadric (1:k) 5 2-(49:k)⁻¹ • OppositeHomogeneousQuadrics.quadric (1:k) 5 0] i := by
  letI : Infinite k := Infinite.of_injective (fun n : ℕ => (n:k)) Nat.cast_injective
  apply MvPolynomial.funext
  intro x
  fin_cases i
  all_goals simp [OppositeHomogeneousQuadrics.quadric,OppositeHomogeneousQuadrics.F0,
    OppositeHomogeneousQuadrics.F1,OppositeHomogeneousQuadrics.F2,OppositePolynomials.A,
    sourceEquation,scale, map_ofNat,Algebra.smul_def]
  all_goals norm_num
  all_goals ring

lemma forward_ideal : oIdeal.toIdeal ≤ Ideal.comap (scale (7:k)) sIdeal.toIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change scale (7:k) (OppositeHomogeneousQuadrics.quadric (1:k) 5 i)∈sIdeal.toIdeal
  rw [forward_equation]
  have hs (a : Fin 3) : sourceEquation k a∈sIdeal.toIdeal := Ideal.subset_span ⟨a,rfl⟩
  fin_cases i
  · exact Ideal.mul_mem_left _ _ (hs 0)
  · exact Ideal.sub_mem _ (hs 1) (hs 0)
  · exact Ideal.sub_mem _ (hs 2) (hs 0)
lemma backward_ideal : sIdeal.toIdeal ≤ Ideal.comap (scale (7⁻¹:k)) oIdeal.toIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change scale (7⁻¹:k) (sourceEquation k i)∈oIdeal.toIdeal
  rw [backward_equation]
  have hs (a : Fin 3) : OppositeHomogeneousQuadrics.quadric (1:k) 5 a∈oIdeal.toIdeal := Ideal.subset_span ⟨a,rfl⟩
  have h0 : (49:k)⁻¹ • OppositeHomogeneousQuadrics.quadric (1:k) 5 0∈oIdeal.toIdeal :=
    (oIdeal.toIdeal.restrictScalars k).smul_mem _ (hs 0)
  fin_cases i
  · simpa using oIdeal.toIdeal.neg_mem h0
  · exact Ideal.sub_mem _ (hs 1) h0
  · exact Ideal.sub_mem _ (hs 2) h0

/-- A graded quotient map retaining the actual homogeneous ideals. -/
def quotientHom (I J : HomogeneousIdeal (ambientGrading (k:=k)))
    (f : ambientGrading (k:=k) →+*ᵍ ambientGrading (k:=k)) (h : I.toIdeal≤Ideal.comap f J.toIdeal) :
    quotGrading ambientGrading I.toIdeal →+*ᵍ quotGrading ambientGrading J.toIdeal where
  __ := Ideal.quotientMap J.toIdeal f h
  map_mem {i} {a} ha := by
    obtain ⟨p,hp,rfl⟩ := (mem_quotGrading_iff _ _).mp ha
    exact mk_mem_quotGrading _ _ (f.map_mem hp)
abbrev forward := quotientHom (oIdeal (k:=k)) sIdeal (scale (7:k)) forward_ideal
abbrev backward := quotientHom (sIdeal (k:=k)) oIdeal (scale (7⁻¹:k)) backward_ideal
lemma scale_inverse : (scale (7:k)).toRingHom.comp (scale (7⁻¹:k)).toRingHom=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a;simp
  · intro j;by_cases hj:j=3
    · simp only [RingHom.comp_apply,GradedRingHom.coe_toRingHom,scale_X,if_pos hj,map_mul,scale_C]
      letI : Infinite k := Infinite.of_injective (fun n : ℕ => (n:k)) Nat.cast_injective
      apply MvPolynomial.funext
      intro x
      simp
    · simp [hj]
lemma scale_inverse' : (scale (7⁻¹:k)).toRingHom.comp (scale (7:k)).toRingHom=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a;simp
  · intro j;by_cases hj:j=3
    · simp only [RingHom.comp_apply,GradedRingHom.coe_toRingHom,scale_X,if_pos hj,map_mul,scale_C]
      letI : Infinite k := Infinite.of_injective (fun n : ℕ => (n:k)) Nat.cast_injective
      apply MvPolynomial.funext
      intro x
      simp
    · simp [hj]
lemma forward_backward : (forward (k:=k)).comp backward = GradedRingHom.id _ := by
  ext x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk sIdeal.toIdeal (scale (7:k) (scale (7⁻¹:k) p))=Ideal.Quotient.mk sIdeal.toIdeal p
  exact congrArg (Ideal.Quotient.mk sIdeal.toIdeal) (RingHom.congr_fun scale_inverse p)
lemma backward_forward : (backward (k:=k)).comp forward = GradedRingHom.id _ := by
  ext x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk oIdeal.toIdeal (scale (7⁻¹:k) (scale (7:k) p))=Ideal.Quotient.mk oIdeal.toIdeal p
  exact congrArg (Ideal.Quotient.mk oIdeal.toIdeal) (RingHom.congr_fun scale_inverse' p)
lemma forward_surjective : Function.Surjective (forward (k:=k)) := by
  intro a
  exact ⟨backward a, DFunLike.congr_fun forward_backward a⟩
lemma backward_surjective : Function.Surjective (backward (k:=k)) := by
  intro a
  exact ⟨forward a, DFunLike.congr_fun backward_forward a⟩
end FourCorner.ThetaOppositeComparison
#print axioms FourCorner.ThetaOppositeComparison.forward_backward
#print axioms FourCorner.ThetaOppositeComparison.backward_forward
