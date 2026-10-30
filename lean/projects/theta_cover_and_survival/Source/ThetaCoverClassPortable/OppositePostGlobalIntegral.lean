import ThetaCoverClassPortable.IntegralTwoOpen

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace FourCorner.OppositeProjective.PostIntegral
open OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual full three-quadric projective scheme is integral.
The P-chart proof uses monic boundary regularity and the genuine homogeneous overlap. -/
theorem literal_projective_integral {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsIntegral (OppositeProjective.curve mu nu) := by
  let UT : (curve mu nu).Opens := Proj.basicOpen (quotientGrading mu nu) (t mu nu)
  let UP : (curve mu nu).Opens := Proj.basicOpen (quotientGrading mu nu) (p mu nu)
  letI := HighChart.chart_isDomain hm hn hA hB hS
  letI := pChart_isDomain hm hn hA hB hS
  haveI : IsIntegral UT.toScheme :=
    IsIntegral.of_isIso (Proj.basicOpenIsoSpec (quotientGrading mu nu) (t mu nu) (ht mu nu) one_pos).inv
  haveI : IsIntegral UP.toScheme :=
    IsIntegral.of_isIso (Proj.basicOpenIsoSpec (quotientGrading mu nu) (p mu nu) (hp mu nu) one_pos).inv
  have hne : ((UT : Set (curve mu nu)) ∩ (UP : Set (curve mu nu))).Nonempty := by
    letI := overlap_nontrivial mu nu
    let x : Spec (.of (overlapRing mu nu)) := Classical.choice inferInstance
    let y := Proj.awayι (quotientGrading mu nu) (p mu nu*t mu nu)
      (SetLike.mul_mem_graded (hp mu nu) (ht mu nu)) (by decide : 0 < 1+1) x
    have hy : y ∈ Proj.basicOpen (quotientGrading mu nu) (p mu nu*t mu nu) := by
      rw [← Proj.opensRange_awayι (quotientGrading mu nu) (p mu nu*t mu nu)
        (SetLike.mul_mem_graded (hp mu nu) (ht mu nu)) (by decide : 0 < 1+1)]
      exact ⟨x,rfl⟩
    rw [Proj.basicOpen_mul] at hy
    exact ⟨y,hy.2,hy.1⟩
  exact integral_two_open UT UP (PostChart.two_charts_cover mu nu) hne

theorem rational_literal_projective_integral (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu/nu) (hl : mu/nu < 2) : IsIntegral (OppositeProjective.curve mu nu) := by
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  exact literal_projective_integral hm hn (rational_A_ne_zero mu nu hn)
    (rational_B_ne_zero mu nu hn hp hl) (rational_S_ne_zero mu nu hn)

end FourCorner.OppositeProjective.PostIntegral
#print axioms FourCorner.OppositeProjective.PostIntegral.literal_projective_integral
#print axioms FourCorner.OppositeProjective.PostIntegral.rational_literal_projective_integral
