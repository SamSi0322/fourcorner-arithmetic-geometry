import ThetaCoverClassPortable.OppositePostAffineSmooth

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FourCorner.OppositeProjective.PostSmooth
open HighChart OppositePolynomials

abbrev rationalT (mu nu : ℚ) :=
  Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (4 : Fin 5))

/-- The actual chart isomorphism is over the original rational base map.
The morphism equality follows from uniqueness of a unital ring map out of Q. -/
lemma rational_chartIso_over (mu nu : ℚ) :
    (chartSchemeIso mu nu).inv ≫
      (Proj.basicOpen (quotientGrading mu nu) (rationalT mu nu)).ι ≫ toBase mu nu =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (affineRing mu nu))) := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

/-- Smoothness of the actual T-open structural morphism of the literal rational Proj. -/
theorem actual_rational_Tchart_smooth (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    SmoothOfRelativeDimension 1
      ((Proj.basicOpen (quotientGrading mu nu) (rationalT mu nu)).ι ≫ toBase mu nu) := by
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  have hspec := affine_smooth hm hn (rational_A_ne_zero mu nu hn)
    (rational_B_ne_zero mu nu hn hp hl) (rational_S_ne_zero mu nu hn)
  have heq : (Proj.basicOpen (quotientGrading mu nu) (rationalT mu nu)).ι ≫ toBase mu nu =
      (chartSchemeIso mu nu).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (affineRing mu nu))) := by
    rw [← rational_chartIso_over mu nu]
    simp
  rw [heq]
  letI := hspec
  change SmoothOfRelativeDimension (0 + 1)
    ((chartSchemeIso mu nu).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (affineRing mu nu))))
  infer_instance

end FourCorner.OppositeProjective.PostSmooth
#print axioms FourCorner.OppositeProjective.PostSmooth.rational_chartIso_over
#print axioms FourCorner.OppositeProjective.PostSmooth.actual_rational_Tchart_smooth
