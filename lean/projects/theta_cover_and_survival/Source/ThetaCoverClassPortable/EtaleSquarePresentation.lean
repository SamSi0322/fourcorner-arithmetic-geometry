import ThetaCoverClassPortable.ParametricPolynomialLift
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

/-- Every actual etale algebra has an actual square submersive presentation.
The identity indexing of variables and relations is proved from relative dimension zero. -/
theorem etale_exists_square_presentation [Algebra.Etale A S] :
    ∃ (β : Type) (_ : Finite β) (P : Algebra.SubmersivePresentation A S β β),
      P.map=id := by
  have hi : Algebra.IsStandardSmoothOfRelativeDimension 0 A S :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨ι,β,hβ,hι,P,hP⟩ := hi.out
  letI := hβ
  letI := hι
  have hc : Nat.card ι ≤ Nat.card β := by
    change Nat.card ι-Nat.card β=0 at hP
    omega
  let e : β≃ι := Equiv.ofBijective P.map (P.map_inj.bijective_of_nat_card_le hc)
  refine ⟨β,hβ,P.reindex e (Equiv.refl β),?_⟩
  funext i
  exact e.symm_apply_apply i

variable {A S} {β : Type} [Fintype β] [DecidableEq β]
  (P : Algebra.SubmersivePresentation A S β β) (hP : P.map=id)
  {R K : Type*} [CommRing R] [Algebra R A] [Algebra R S] [IsScalarTower R A S]
  [Field K] [Algebra R K] (f : S →ₐ[R] K)

def evaluatedPresentationJacobian : Matrix β β K :=
  fun i j => f (aeval P.val (pderiv j (P.relation i)))

include hP in
theorem evaluatedPresentationJacobian_det :
    (evaluatedPresentationJacobian P f).det=f P.jacobian := by
  have hm : evaluatedPresentationJacobian P f =
      (f.toRingHom.comp (aeval P.val).toRingHom).mapMatrix P.jacobiMatrix.transpose := by
    ext i j
    simp only [evaluatedPresentationJacobian,RingHom.mapMatrix_apply,Matrix.map_apply,
      Matrix.transpose_apply,P.jacobiMatrix_apply,hP,id_eq,RingHom.comp_apply]
    rfl
  rw [hm,←RingHom.map_det,Matrix.det_transpose]
  rw [P.jacobian_eq_jacobiMatrix_det,P.algebraMap_apply]
  rfl

include hP in
/-- The Jacobian at any genuine field-valued point of an etale presentation is nonzero. -/
theorem evaluatedPresentationJacobian_det_ne_zero :
    (evaluatedPresentationJacobian P f).det≠0 := by
  rw [evaluatedPresentationJacobian_det P hP f]
  exact (P.jacobian_isUnit.map f.toMonoidHom).ne_zero

end FourCorner.ThetaLocalSurvival.StrongTopology
