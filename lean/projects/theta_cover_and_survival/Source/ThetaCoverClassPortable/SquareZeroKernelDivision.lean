import ThetaCoverClassPortable.ActualSquareZeroKernels

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

/-- Actual change of the test algebra from the split extension QQ⊕I
into R, restricted to the genuine reduction kernels. -/
def splitToIdeal : tangentPoints G I →* idealKernel G R I where
  toFun P := ⟨change G (Augmented.squareZeroToRing R I hI) P.val,by
    change change G (Ideal.Quotient.mkₐ ℚ I) (change G (Augmented.squareZeroToRing R I hI) P.val)=1
    rw [change_comp,Augmented.squareZeroToRing_reduction,←change_comp]
    rw [show change G (TrivSqZeroExt.fstHom ℚ ℚ I) P.val=1 from P.property,map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

variable (A : Type) [CommRing A] [Algebra ℚ A]
variable (j : pointObject A ⟶ G) [IsOpenImmersion j.left]
variable (ε : A →ₐ[ℚ] ℚ) (he : pointChange ε ≫ j=1)

theorem idealChartLift_split (P : tangentPoints G I) :
    idealChartLift G R I hI A j ε he (splitToIdeal G R I hI P)=
      pointChange (Augmented.squareZeroToRing R I hI) ≫ chartLift G A j ε he P := by
  apply Over.OverMorphism.ext
  apply (cancel_mono j.left).mp
  exact congrArg (fun f : pointObject R ⟶ G => f.left)
    (show idealChartLift G R I hI A j ε he (splitToIdeal G R I hI P) ≫ j=
      (pointChange (Augmented.squareZeroToRing R I hI) ≫ chartLift G A j ε he P) ≫ j by
      rw [idealChartLift_comp,Category.assoc,chartLift_comp]
      rfl)

theorem idealChart_split (P : tangentPoints G I) :
    (idealChartEquiv G R I hI A j ε he (splitToIdeal G R I hI P)).val=
      (Augmented.squareZeroToRing R I hI).comp (chartPointsEquiv G A j ε he P).val := by
  change pointToAlgHom A R (idealChartLift G R I hI A j ε he (splitToIdeal G R I hI P))=_
  rw [idealChartLift_split,pointToAlgHom_natural]
  rfl

theorem idealDeriv_split (P : tangentPoints G I) :
    idealPointDerivEquiv G R I hI A j ε he (splitToIdeal G R I hI P)=
      pointDerivEquiv G A j ε he P := by
  apply (Augmented.idealLiftEquiv ε R I hI).injective
  apply Subtype.ext
  change Augmented.idealLift ε R I hI (idealPointDerivEquiv G R I hI A j ε he (splitToIdeal G R I hI P))=
    Augmented.idealLift ε R I hI (pointDerivEquiv G A j ε he P)
  rw [idealPointDeriv_lift,←Augmented.splitLift_to_idealLift,pointDeriv_lift,idealChart_split]

include ε he in
theorem splitToIdeal_bijective : Function.Bijective (splitToIdeal G R I hI) := by
  constructor
  · intro P Q h
    apply (pointDerivEquiv G A j ε he).injective
    rw [←idealDeriv_split G R I hI A j ε he P,←idealDeriv_split G R I hI A j ε he Q,h]
  · intro P
    refine ⟨(pointDerivEquiv G A j ε he).symm (idealPointDerivEquiv G R I hI A j ε he P),?_⟩
    apply (idealPointDerivEquiv G R I hI A j ε he).injective
    rw [idealDeriv_split,Equiv.apply_symm_apply]

def splitToIdealMulEquiv : tangentPoints G I ≃* idealKernel G R I :=
  MulEquiv.ofBijective (splitToIdeal G R I hI) (splitToIdeal_bijective G R I hI A j ε he)

/-- The exact additive derivation correspondence for an arbitrary
actual square-zero quotient R/I, including its genuine group law. -/
def idealPointDerivAddEquiv : Additive (idealKernel G R I) ≃+ Augmented.augDeriv ε I where
  toFun P := idealPointDerivEquiv G R I hI A j ε he P.toMul
  invFun d := Additive.ofMul ((idealPointDerivEquiv G R I hI A j ε he).symm d)
  left_inv P := congrArg Additive.ofMul ((idealPointDerivEquiv G R I hI A j ε he).symm_apply_apply P.toMul)
  right_inv d := (idealPointDerivEquiv G R I hI A j ε he).apply_symm_apply d
  map_add' P Q := by
    obtain ⟨p,hp⟩ := (splitToIdeal_bijective G R I hI A j ε he).surjective P.toMul
    obtain ⟨q,hq⟩ := (splitToIdeal_bijective G R I hI A j ε he).surjective Q.toMul
    change idealPointDerivEquiv G R I hI A j ε he (P.toMul*Q.toMul)=
      idealPointDerivEquiv G R I hI A j ε he P.toMul+idealPointDerivEquiv G R I hI A j ε he Q.toMul
    rw [←hp,←hq,←map_mul,idealDeriv_split,idealDeriv_split,idealDeriv_split,pointDeriv_mul]

/-- Unique correction for EVERY actual square-zero extension, with no
chosen affine chart or derivation data in the hypotheses. -/
theorem actual_square_zero_kernel_unique_root (G : Over base) [GrpObj G]
    (R : Type) [CommRing R] [Algebra ℚ R] (I : Ideal R) (hI : I^2=⊥)
    (m : ℕ) (hm : 0<m) (P : idealKernel G R I) : ∃! Q : idealKernel G R I,Q^m=P := by
  obtain ⟨A,qmap,h⟩ := exists_identity_chart G
  letI : Algebra ℚ A := qmap.toAlgebra
  obtain ⟨j,ε,hj,he⟩ := h
  letI := hj
  let e := splitToIdealMulEquiv G R I hI A j ε he
  obtain ⟨Q,hQ,huniq⟩ := actual_infinitesimal_unique_root G I m hm (e.symm P)
  refine ⟨e Q,?_,?_⟩
  · change (e Q)^m=P
    rw [←map_pow,hQ,e.apply_symm_apply]
  · intro T hT
    apply e.symm.injective
    rw [e.symm_apply_apply]
    apply huniq
    change (e.symm T)^m=e.symm P
    rw [←map_pow,hT]

/-- In particular, [m] has no nonzero infinitesimal kernel in
characteristic zero. This is actual functor-of-points injectivity. -/
theorem actual_square_zero_kernel_pow_injective (G : Over base) [GrpObj G]
    (R : Type) [CommRing R] [Algebra ℚ R] (I : Ideal R) (hI : I^2=⊥)
    (m : ℕ) (hm : 0<m) : Function.Injective (fun P : idealKernel G R I => P^m) := by
  intro P Q h
  obtain ⟨T,_,huniq⟩ := actual_square_zero_kernel_unique_root G R I hI m hm (P^m)
  exact (huniq P rfl).trans (huniq Q h.symm).symm

end FourCorner.ThetaLocalSurvival.Infinitesimal
