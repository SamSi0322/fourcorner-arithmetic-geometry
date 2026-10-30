import ThetaLocalSurvivalPortable.AffineIdentityChart
import ThetaLocalSurvivalPortable.SquareZeroIdealDerivations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication
variable (G : Over base) [GrpObj G]
variable (R : Type) [CommRing R] [Algebra ℚ R] (I : Ideal R) (hI : I^2=⊥)

def idealReduction : points G R →* points G (R⧸I) := change G (Ideal.Quotient.mkₐ ℚ I)
abbrev idealKernel := (idealReduction G R I).ker

include hI in
theorem quotient_points_surjective : Function.Surjective (pointChange (Ideal.Quotient.mkₐ ℚ I)).left := by
  let f := (Ideal.Quotient.mkₐ ℚ I).toRingHom
  have hker : RingHom.ker f≤nilradical R := by
    intro x hx
    have hxI : x∈I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    apply mem_nilradical.mpr
    refine ⟨2,?_⟩
    have hh := Ideal.mul_mem_mul hxI hxI
    rw [←pow_two,hI] at hh
    simpa only [pow_two,Ideal.mem_bot] using hh
  have hpower : ∀q : R⧸I,∃n : ℕ,0<n ∧ q^n∈f.range := by
    intro q
    obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨1,by decide,r,by simpa [f] using hr⟩
  exact (PrimeSpectrum.isHomeomorph_comap f hpower hker).surjective

variable (A : Type) [CommRing A] [Algebra ℚ A]
variable (j : pointObject A ⟶ G) [IsOpenImmersion j.left]
variable (ε : A →ₐ[ℚ] ℚ) (he : pointChange ε ≫ j=1)

include he in
theorem augmentation_point_basechange (B : Type) [CommRing B] [Algebra ℚ B] :
    pointChange ((Algebra.ofId ℚ B).comp ε) ≫ j=1 := by
  rw [←pointChange_comp,Category.assoc,he,MonObj.comp_one]

include ε he hI in
theorem ideal_range_in_chart (P : idealKernel G R I) : Set.range P.val.left⊆Set.range j.left := by
  rintro _ ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := quotient_points_surjective R I hI x
  have hP := congrArg (fun f : pointObject (R⧸I) ⟶ G => f.left y) P.property
  have hE := congrArg (fun f : pointObject (R⧸I) ⟶ G => f.left y)
    (augmentation_point_basechange G A j ε he (R⧸I))
  change P.val.left ((pointChange (Ideal.Quotient.mkₐ ℚ I)).left y)=
    (1 : pointObject (R⧸I) ⟶ G).left y at hP
  change j.left ((pointChange ((Algebra.ofId ℚ (R⧸I)).comp ε)).left y)=
    (1 : pointObject (R⧸I) ⟶ G).left y at hE
  rw [hy] at hP
  exact ⟨_,hE.trans hP.symm⟩

def idealChartLift (P : idealKernel G R I) : pointObject R ⟶ pointObject A :=
  Over.homMk (IsOpenImmersion.lift j.left P.val.left (ideal_range_in_chart G R I hI A j ε he P)) (by
    rw [←j.w,←Category.assoc,IsOpenImmersion.lift_fac]
    exact P.val.w)

theorem idealChartLift_comp (P : idealKernel G R I) : idealChartLift G R I hI A j ε he P ≫ j=P.val := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem idealChartLift_reduction (P : idealKernel G R I) :
    pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ idealChartLift G R I hI A j ε he P=
      pointChange ((Algebra.ofId ℚ (R⧸I)).comp ε) := by
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  exact congrArg (fun f : pointObject (R⧸I) ⟶ G => f.left)
    (show pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ idealChartLift G R I hI A j ε he P ≫ j=
      pointChange ((Algebra.ofId ℚ (R⧸I)).comp ε) ≫ j by
      rw [idealChartLift_comp,augmentation_point_basechange G A j ε he]
      exact P.property)

def idealChartAlgebraMap (P : idealKernel G R I) : Augmented.idealLifts ε R I :=
  ⟨pointToAlgHom A R (idealChartLift G R I hI A j ε he P),by
    apply pointChange_injective
    rw [←pointChange_comp,pointChange_pointToAlgHom,idealChartLift_reduction]⟩

def idealAlgebraMapPoint (f : Augmented.idealLifts ε R I) : idealKernel G R I :=
  ⟨pointChange f.val ≫ j,by
    change pointChange (Ideal.Quotient.mkₐ ℚ I) ≫ (pointChange f.val ≫ j)=1
    rw [←Category.assoc,pointChange_comp,f.property,augmentation_point_basechange G A j ε he]⟩

def idealChartEquiv : idealKernel G R I ≃ Augmented.idealLifts ε R I where
  toFun := idealChartAlgebraMap G R I hI A j ε he
  invFun := idealAlgebraMapPoint G R I A j ε he
  left_inv P := by
    apply Subtype.ext
    change pointChange (pointToAlgHom A R (idealChartLift G R I hI A j ε he P)) ≫ j=P.val
    rw [pointChange_pointToAlgHom,idealChartLift_comp]
  right_inv f := by
    apply Subtype.ext
    apply pointChange_injective
    change pointChange (pointToAlgHom A R
      (idealChartLift G R I hI A j ε he (idealAlgebraMapPoint G R I A j ε he f)))=pointChange f.val
    rw [pointChange_pointToAlgHom]
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).mp
    exact congrArg (fun g : pointObject R ⟶ G => g.left)
      (idealChartLift_comp G R I hI A j ε he (idealAlgebraMapPoint G R I A j ε he f))

def idealPointDerivEquiv : idealKernel G R I ≃ Augmented.augDeriv ε I :=
  (idealChartEquiv G R I hI A j ε he).trans (Augmented.idealLiftEquiv ε R I hI).symm

theorem idealPointDeriv_lift (P : idealKernel G R I) :
    Augmented.idealLift ε R I hI (idealPointDerivEquiv G R I hI A j ε he P)=
      (idealChartEquiv G R I hI A j ε he P).val :=
  congrArg Subtype.val ((Augmented.idealLiftEquiv ε R I hI).apply_symm_apply
    (idealChartEquiv G R I hI A j ε he P))

end FourCorner.ThetaLocalSurvival.Infinitesimal
