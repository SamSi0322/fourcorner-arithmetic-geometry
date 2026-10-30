import ThetaLocalSurvivalPortable.AffinePointAlgebra
import ThetaLocalSurvivalPortable.AugmentedDerivations
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj FourCorner.ThetaLocalSurvival.SquareZeroScalars
namespace FourCorner.ThetaLocalSurvival.Infinitesimal
open Multiplication

variable (M : Type) [AddCommGroup M] [Module ℚ M]

theorem infinitesimal_reduction_surjective :
    Function.Surjective (pointChange (TrivSqZeroExt.fstHom ℚ ℚ M)).left := by
  let f := (TrivSqZeroExt.fstHom ℚ ℚ M).toRingHom
  have hker : RingHom.ker f≤nilradical (sq M) := by
    intro x hx
    have hx0 : x.fst=0 := hx
    apply mem_nilradical.mpr
    refine ⟨2,?_⟩
    apply TrivSqZeroExt.ext <;> simp [pow_two,TrivSqZeroExt.fst_mul,TrivSqZeroExt.snd_mul,hx0]
  have hpower : ∀q : ℚ,∃n : ℕ,0<n ∧ q^n∈f.range := by
    intro q
    exact ⟨1,by decide,TrivSqZeroExt.inl q,by simp [f]⟩
  exact (PrimeSpectrum.isHomeomorph_comap f hpower hker).surjective

variable {M} (G : Over base) [GrpObj G]
variable (A : Type) [CommRing A] [Algebra ℚ A]
variable (j : pointObject A ⟶ G) [IsOpenImmersion j.left]
variable (ε : A →ₐ[ℚ] ℚ) (he : pointChange ε ≫ j=1)

include ε he in
theorem infinitesimal_range_in_chart (P : tangentPoints G M) :
    Set.range P.val.left⊆Set.range j.left := by
  rintro _ ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := infinitesimal_reduction_surjective M x
  have hP := congrArg (fun f : pointObject ℚ ⟶ G => f.left y) P.property
  have hE := congrArg (fun f : pointObject ℚ ⟶ G => f.left y) he
  change P.val.left ((pointChange (TrivSqZeroExt.fstHom ℚ ℚ M)).left y)=
    (1 : pointObject ℚ ⟶ G).left y at hP
  change j.left ((pointChange ε).left y)=(1 : pointObject ℚ ⟶ G).left y at hE
  rw [hy] at hP
  exact ⟨(pointChange ε).left y,hE.trans hP.symm⟩

def chartLift (P : tangentPoints G M) : pointObject (sq M) ⟶ pointObject A :=
  Over.homMk (IsOpenImmersion.lift j.left P.val.left (infinitesimal_range_in_chart G A j ε he P)) (by
    rw [←j.w,←Category.assoc,IsOpenImmersion.lift_fac]
    exact P.val.w)

theorem chartLift_comp (P : tangentPoints G M) : chartLift G A j ε he P ≫ j=P.val := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem chartLift_reduction (P : tangentPoints G M) :
    pointChange (TrivSqZeroExt.fstHom ℚ ℚ M) ≫ chartLift G A j ε he P=pointChange ε := by
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  have h := congrArg (fun f : pointObject ℚ ⟶ G => f.left)
    (show pointChange (TrivSqZeroExt.fstHom ℚ ℚ M) ≫ chartLift G A j ε he P ≫ j=
      pointChange ε ≫ j by rw [chartLift_comp];exact P.property.trans he.symm)
  exact h

def chartAlgebraMap (P : tangentPoints G M) : Augmented.lifts ε (M:=M) :=
  ⟨pointToAlgHom A (sq M) (chartLift G A j ε he P),by
    apply pointChange_injective
    rw [←pointChange_comp,pointChange_pointToAlgHom,chartLift_reduction]⟩

def algebraMapPoint (f : Augmented.lifts ε (M:=M)) : tangentPoints G M :=
  ⟨pointChange f.val ≫ j,by
    change pointChange (TrivSqZeroExt.fstHom ℚ ℚ M) ≫ (pointChange f.val ≫ j)=1
    rw [←Category.assoc,pointChange_comp,f.property,he]⟩

def chartPointsEquiv : tangentPoints G M ≃ Augmented.lifts ε (M:=M) where
  toFun := chartAlgebraMap G A j ε he
  invFun := algebraMapPoint G A j ε he
  left_inv P := by
    apply Subtype.ext
    change pointChange (pointToAlgHom A (sq M) (chartLift G A j ε he P)) ≫ j=P.val
    rw [pointChange_pointToAlgHom,chartLift_comp]
  right_inv f := by
    apply Subtype.ext
    apply pointChange_injective
    change pointChange (pointToAlgHom A (sq M)
      (chartLift G A j ε he (algebraMapPoint G A j ε he f)))=pointChange f.val
    rw [pointChange_pointToAlgHom]
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).mp
    exact congrArg (fun g : pointObject (sq M) ⟶ G => g.left)
      (chartLift_comp G A j ε he (algebraMapPoint G A j ε he f))

variable {N : Type} [AddCommGroup N] [Module ℚ N]

theorem chartLift_natural (f : M →ₗ[ℚ] N) (P : tangentPoints G M) :
    pointChange (TrivSqZeroExt.map f) ≫ chartLift G A j ε he P=
      chartLift G A j ε he (tangentMap G f P) := by
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  exact congrArg (fun g : pointObject (sq N) ⟶ G => g.left)
    (show (pointChange (TrivSqZeroExt.map f) ≫ chartLift G A j ε he P) ≫ j=
      chartLift G A j ε he (tangentMap G f P) ≫ j by
      rw [Category.assoc,chartLift_comp,chartLift_comp]
      rfl)

theorem chartPoints_natural (f : M →ₗ[ℚ] N) (P : tangentPoints G M) :
    (chartPointsEquiv G A j ε he (tangentMap G f P)).val=
      (TrivSqZeroExt.map f).comp (chartPointsEquiv G A j ε he P).val := by
  change pointToAlgHom A (sq N) (chartLift G A j ε he (tangentMap G f P))=_
  rw [←chartLift_natural,pointToAlgHom_natural]
  rfl

/-- The actual scheme identity kernel is identified with genuine native
derivations in any actual affine identity chart. -/
def pointDerivEquiv : tangentPoints G M ≃ Augmented.augDeriv ε M :=
  (chartPointsEquiv G A j ε he).trans (Augmented.liftEquiv ε).symm

theorem pointDeriv_lift (P : tangentPoints G M) :
    Augmented.lift ε (pointDerivEquiv G A j ε he P)=
      (chartPointsEquiv G A j ε he P).val :=
  congrArg Subtype.val ((Augmented.liftEquiv ε).apply_symm_apply (chartPointsEquiv G A j ε he P))

theorem pointDeriv_natural (f : M →ₗ[ℚ] N) (P : tangentPoints G M) :
    pointDerivEquiv G A j ε he (tangentMap G f P)=
      Augmented.push ε f (pointDerivEquiv G A j ε he P) := by
  apply (Augmented.liftEquiv ε).injective
  apply Subtype.ext
  change Augmented.lift ε (pointDerivEquiv G A j ε he (tangentMap G f P))=
    Augmented.lift ε (Augmented.push ε f (pointDerivEquiv G A j ε he P))
  rw [pointDeriv_lift,←Augmented.lift_natural,pointDeriv_lift,chartPoints_natural]

theorem pointDeriv_one : pointDerivEquiv G A j ε he (1 : tangentPoints G M)=0 := by
  apply (Augmented.liftEquiv ε).injective
  apply Subtype.ext
  change Augmented.lift ε (pointDerivEquiv G A j ε he (1 : tangentPoints G M))=
    Augmented.lift ε (0 : Augmented.augDeriv ε M)
  rw [pointDeriv_lift]
  apply pointChange_injective
  change pointChange (pointToAlgHom A (sq M) (chartLift G A j ε he 1))=_
  rw [pointChange_pointToAlgHom]
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  have hz : Augmented.lift ε (0 : Augmented.augDeriv ε M)=
      (TrivSqZeroExt.inlAlgHom ℚ ℚ M).comp ε := by
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext <;> rfl
  have hf : pointChange (Augmented.lift ε (0 : Augmented.augDeriv ε M)) ≫ j=1 := by
    rw [hz,←pointChange_comp,Category.assoc,he,MonObj.comp_one]
  have hh := (chartLift_comp G A j ε he (1 : tangentPoints G M)).trans hf.symm
  exact congrArg (fun g : pointObject (sq M) ⟶ G => g.left) hh

end FourCorner.ThetaLocalSurvival.Infinitesimal
