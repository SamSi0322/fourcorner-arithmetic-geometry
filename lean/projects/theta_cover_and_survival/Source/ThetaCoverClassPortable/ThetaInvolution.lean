import ThetaCoverClassPortable.ThetaSourceComparison
import ThetaCoverClassPortable.ThetaProjection
noncomputable section
namespace FourCorner.ThetaInvolution
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaOppositeComparison ThetaProjection
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

def ambientSigma : homogeneousSubmodule (Fin 5) k →+*ᵍ homogeneousSubmodule (Fin 5) k where
  __ := eval₂Hom C ![-X 0,-X 1,-X 2,X 3,X 4]
  map_mem {i} {p} hp := by
    have hg (j : Fin 5) : (![-X 0,-X 1,-X 2,X 3,X 4] j : MvPolynomial (Fin 5) k).IsHomogeneous 1 := by
      fin_cases j
      · exact (isHomogeneous_X _ _).neg
      · exact (isHomogeneous_X _ _).neg
      · exact (isHomogeneous_X _ _).neg
      · exact isHomogeneous_X _ _
      · exact isHomogeneous_X _ _
    have h:=hp.eval₂ C _ (fun a=>isHomogeneous_C _ a) hg
    change (eval₂ C ![-X 0,-X 1,-X 2,X 3,X 4] p).IsHomogeneous i
    simpa only [one_mul] using h
lemma equation_sigma (i : Fin 3) : ambientSigma (sourceEquation k i)=sourceEquation k i := by
  fin_cases i <;> simp [ambientSigma,sourceEquation]
lemma ideal_sigma : sIdeal.toIdeal≤Ideal.comap (ambientSigma (k:=k)) sIdeal.toIdeal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change ambientSigma (sourceEquation k i)∈sIdeal.toIdeal
  rw [equation_sigma]
  exact Ideal.subset_span ⟨i,rfl⟩
def sigmaMap := quotientHom (sIdeal (k:=k)) sIdeal ambientSigma ideal_sigma
lemma ambientSigma_sq : (ambientSigma (k:=k)).toRingHom.comp ambientSigma.toRingHom=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a;simp [ambientSigma]
  · intro j;fin_cases j <;> simp [ambientSigma]
lemma sigmaMap_sq : (sigmaMap (k:=k)).comp sigmaMap=GradedRingHom.id _ := by
  ext x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk sIdeal.toIdeal (ambientSigma (ambientSigma p))=Ideal.Quotient.mk sIdeal.toIdeal p
  exact congrArg (Ideal.Quotient.mk sIdeal.toIdeal) (RingHom.congr_fun ambientSigma_sq p)
lemma sigmaMap_surjective : Function.Surjective (sigmaMap (k:=k)) := by
  intro a
  exact ⟨sigmaMap a,DFunLike.congr_fun sigmaMap_sq a⟩
def sigma : C k ⟶ C k :=
  Proj.map (sigmaMap (k:=k)) (ProjectiveClosedImmersion.irrelevant_le_map_of_surjective
    (sigmaMap (k:=k)) (sigmaMap_surjective (k:=k)))
theorem sigma_sq : sigma (k:=k) ≫ sigma=𝟙 _ := by
  unfold sigma
  rw [←Proj.map_comp]
  exact ThetaProjEquality.map_eq_id _ (sigmaMap_sq (k:=k)) _
/-- Actual projective-scheme involution of the literal source. -/
def sigmaAut : C k ≅ C k := ⟨sigma,sigma,sigma_sq,sigma_sq⟩
/-- Its action on the homogeneous coordinate ring is precisely the paper's sign change. -/
theorem sigma_coordinates (j : Fin 5) : sigmaMap (sqmap (k:=k) (X j))=
    ![-sx 0,-sx 1,-sx 2,sx 3,sx 4] j := by
  fin_cases j <;> simp [sigmaMap,quotientHom,ambientSigma,sx]
end FourCorner.ThetaInvolution
#print axioms FourCorner.ThetaInvolution.sigmaAut
#print axioms FourCorner.ThetaInvolution.sigma_coordinates
