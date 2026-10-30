import ThetaLocalSurvivalPortable.SquareZeroGroupCorrection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication
variable (G : Over base) [GrpObj G]
variable (R : Type) [CommRing R] [Algebra ℚ R] (I : Ideal R) (hI : I^2=⊥)
variable (A : Type) [CommRing A] [Algebra ℚ A]
variable (j : pointObject A ⟶ G) [IsOpenImmersion j.left]

include hI in
theorem open_point_range (P : points G R) (P0 : pointObject (R⧸I) ⟶ pointObject A)
    (hred : pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ P=P0 ≫ j) :
    Set.range P.left⊆Set.range j.left := by
  rintro _ ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := quotient_points_surjective R I hI x
  have h := congrArg (fun f : pointObject (R⧸I) ⟶ G => f.left y) hred
  change P.left ((pointChange (Ideal.Quotient.mkₐ ℚ I)).left y)=j.left (P0.left y) at h
  rw [hy] at h
  exact ⟨P0.left y,h.symm⟩

def openPointLift (P : points G R) (P0 : pointObject (R⧸I) ⟶ pointObject A)
    (hred : pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ P=P0 ≫ j) : pointObject R ⟶ pointObject A :=
  Over.homMk (IsOpenImmersion.lift j.left P.left (open_point_range G R I hI A j P P0 hred)) (by
    rw [←j.w,←Category.assoc,IsOpenImmersion.lift_fac]
    exact P.w)

theorem openPointLift_comp (P : points G R) (P0 : pointObject (R⧸I) ⟶ pointObject A)
    (hred : pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ P=P0 ≫ j) :
    openPointLift G R I hI A j P P0 hred ≫ j=P := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem openPointLift_reduction (P : points G R) (P0 : pointObject (R⧸I) ⟶ pointObject A)
    (hred : pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ P=P0 ≫ j) :
    pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ openPointLift G R I hI A j P P0 hred=P0 := by
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  exact congrArg (fun f : pointObject (R⧸I) ⟶ G => f.left)
    (show pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ openPointLift G R I hI A j P P0 hred ≫ j=P0 ≫ j by
      rw [openPointLift_comp,hred])

include j in
/-- Smoothness over QQ gives the genuine native formally smooth QQ
coordinate algebra of every actual affine chart. -/
theorem affine_chart_smooth [Smooth G.hom] : Algebra.Smooth ℚ A := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) := by
    change Smooth (pointObject A).hom
    rw [←j.w]
    infer_instance
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P:=@Smooth)).mp h)

end FourCorner.ThetaLocalSurvival.Infinitesimal
