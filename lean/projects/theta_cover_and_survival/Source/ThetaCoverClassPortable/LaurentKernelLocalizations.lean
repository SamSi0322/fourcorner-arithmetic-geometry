import ThetaCoverClassPortable.LaurentPresentationKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology

/-- Localization of the actual kernel restriction, obtained from native
localization exactness and the actual commuting restriction square. -/
theorem kernelRestriction_localizes
    {A B M N P Q : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    [Module B Q] [IsScalarTower A B Q]
    (s : Submonoid A) [IsLocalization s B]
    (f : M →ₗ[A] N) (g : P →ₗ[A] Q)
    [IsLocalizedModule s f] [IsLocalizedModule s g]
    (h : M →ₗ[A] P) (k : N →ₗ[A] Q) (comm : k.comp f=g.comp h) :
    IsLocalizedModule s (f.restrict (p := LinearMap.ker h) (q := LinearMap.ker k) (fun x hx => show k (f x)=0 by
      rw [←LinearMap.comp_apply,comm,LinearMap.comp_apply,LinearMap.mem_ker.mp hx,map_zero])) := by
  have he : IsLocalizedModule.map s f g h = k :=
    IsLocalizedModule.linearMap_ext s f g ((IsLocalizedModule.map_comp s f g h).trans comm.symm)
  subst k
  exact LinearMap.toKerLocalized_isLocalizedModule B s f g h

variable {R : Type u} [CommRing R] {ι : Type*} [Fintype ι]
  {S : TwoChartCech.Sections (laurentCover R)} {d : ℤ}
namespace LaurentPresentation
variable (p : LaurentPresentation S d ι)

 theorem kernel_positive_localizes (h : PositiveLocalizes S) :
    PositiveLocalizes p.kernelSections := by
  letI : Module R[X] S.M01 := Module.compHom S.M01 (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  letI : Module R[X] (freeTwistSections (R := R) (ι := ι) d).M01 := Module.compHom (freeTwistSections (R := R) (ι := ι) d).M01
    (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  haveI : IsScalarTower R[X] (LaurentPolynomial R) S.M01 := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower R[X] (LaurentPolynomial R) (freeTwistSections (R := R) (ι := ι) d).M01 := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalizedModule.Away (X : R[X]) (positiveRestriction S) := h
  letI : IsLocalizedModule.Away (X : R[X])
      (positiveRestriction (freeTwistSections (R := R) (ι := ι) d)) := freeTwist_positive_localizes d
  have hc : (p.overlap.restrictScalars R[X]).comp
      (positiveRestriction (freeTwistSections (R := R) (ι := ι) d)) =
      (positiveRestriction S).comp p.positive := by
    ext x
    exact (p.comm_positive x).symm
  exact kernelRestriction_localizes (B := LaurentPolynomial R) (Submonoid.powers (X : R[X]))
    (positiveRestriction (freeTwistSections (R := R) (ι := ι) d)) (positiveRestriction S)
    p.positive (p.overlap.restrictScalars R[X]) hc

 theorem kernel_negative_localizes (h : NegativeLocalizes S) :
    NegativeLocalizes p.kernelSections := by
  letI : Algebra R[X] (LaurentPolynomial R) :=
    (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom.toAlgebra
  letI : Module R[X] (LaurentPolynomial R) := Module.compHom (LaurentPolynomial R)
    (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom
  letI : Module R[X] S.M01 := Module.compHom S.M01
    (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom
  letI : Module R[X] (freeTwistSections (R := R) (ι := ι) d).M01 := Module.compHom (freeTwistSections (R := R) (ι := ι) d).M01
    (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom
  haveI : IsLocalization.Away (X : R[X]) (LaurentPolynomial R) :=
    FourCorner.StandardLaurentCech.negative_localization
  haveI : IsScalarTower R[X] (LaurentPolynomial R) S.M01 := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower R[X] (LaurentPolynomial R) (freeTwistSections (R := R) (ι := ι) d).M01 := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalizedModule.Away (X : R[X]) (negativeRestriction S) := h
  letI : IsLocalizedModule.Away (X : R[X])
      (negativeRestriction (freeTwistSections (R := R) (ι := ι) d)) := freeTwist_negative_localizes d
  have hc : (p.overlap.restrictScalars R[X]).comp
      (negativeRestriction (freeTwistSections (R := R) (ι := ι) d)) =
      (negativeRestriction S).comp p.negative := by
    ext x
    exact (p.comm_negative x).symm
  exact kernelRestriction_localizes (B := LaurentPolynomial R) (Submonoid.powers (X : R[X]))
    (negativeRestriction (freeTwistSections (R := R) (ι := ι) d)) (negativeRestriction S)
    p.negative (p.overlap.restrictScalars R[X]) hc
end LaurentPresentation
end FourCorner.FiniteMapCohomology
