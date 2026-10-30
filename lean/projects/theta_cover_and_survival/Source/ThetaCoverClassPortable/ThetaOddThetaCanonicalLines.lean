import ThetaCoverClassPortable.ThetaActualOddThetaClasses

noncomputable section
set_option autoImplicit false
open AlgebraicCurve AlgebraicGeometry KaehlerDifferential CategoryTheory
namespace FourCorner.ThetaOddThetaCanonicalLines
open ThetaDGeometricModel DivisorPicClassification ThetaActualOddThetaClasses
open ThetaDNaturalGlobalDifferentials
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance sectionsModule (U : geometricD.Opens) : Module K Γ(toBase.kaehler,U) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler U

/-- ACTUAL original-coordinate plane forms, passed through the natural global
sheaf map and actual generic germ. No abstract equal-dimension equivalence. -/
def planeToField : (Fin 3→K) →ₗ[K] Ω[field⁄K] :=
  genericGerm.comp (planeGlobalSectionEquiv.toLinearMap.comp
    (dotProductEquiv K (Fin 3)).toLinearMap)

 theorem planeToField_formula (a : Fin 3→K) : planeToField a=
    (algebraMap K field (a 2)+algebraMap K field (a 0)*ThetaDFieldCoordinates.x+
      algebraMap K field (a 1)*ThetaDFieldCoordinates.y) • ThetaDActualDifferential.omega :=
  actual_global_line_germ a

 theorem genericGerm_injective : Function.Injective genericGerm := by
  intro s t h
  apply globalRegularEquiv.injective
  apply Subtype.ext
  simpa only [globalRegularEquiv_germ] using h

 theorem planeToField_injective : Function.Injective planeToField :=
  genericGerm_injective.comp (planeGlobalSectionEquiv.injective.comp
    (dotProductEquiv K (Fin 3)).injective)

 theorem planeToField_ne_zero {a : Fin 3→K} (ha : a≠0) : planeToField a≠0 := by
  intro h
  exact ha (planeToField_injective (h.trans (map_zero planeToField).symm))

 theorem exists_plane_of_regular {ω : Ω[field⁄K]} (hω : ω≠0)
    (hreg : ω∈regularDifferentials K field) :
    ∃a : Fin 3→K,a≠0 ∧ planeToField a=ω := by
  let s := globalRegularEquiv.symm ⟨ω,hreg⟩
  let a := (dotProductEquiv K (Fin 3)).symm (planeGlobalSectionEquiv.symm s)
  have hg : genericGerm s=ω := by
    rw [←globalRegularEquiv_germ]
    exact congrArg Subtype.val (globalRegularEquiv.apply_symm_apply ⟨ω,hreg⟩)
  have heq : planeToField a=ω := by
    change genericGerm (planeGlobalSectionEquiv (dotProductEquiv K (Fin 3) a))=ω
    simp only [a,LinearEquiv.apply_symm_apply]
    exact hg
  refine ⟨a,?_,heq⟩
  intro ha
  rw [ha,map_zero] at heq
  exact hω heq.symm

/-- Reverse odd-theta to the genuine canonical plane line on original D_Qbar.
The representative divisor and projective line are proved unique, the latter
as the exact nonzero-scalar relation on the ORIGINAL coordinate triples. -/
theorem odd_theta_unique_canonical_line (c : ActualPic) (hc : IsOddThetaClass c) :
    ∃ (B : ActualDivisor) (a : Fin 3→K) (ha : a≠0),
      0≤B ∧ divisorClass B=c ∧ Divisor.degree B=2 ∧ ell B=1 ∧
      canonicalDivisorOf (planeToField_ne_zero ha)=(2:ℕ) • B ∧
      (∀E : ActualDivisor,0≤E → divisorClass E=c → E=B) ∧
      ∀(b : Fin 3→K)(hb : b≠0),
        canonicalDivisorOf (planeToField_ne_zero hb)=(2:ℕ) • B →
        ∃u : K,u≠0 ∧ b=u • a := by
  obtain ⟨B,hB,hcl,hdeg,hell,huniq,ω,hω,hreg,hcan⟩ := actual_odd_theta_effective_unique c hc
  obtain ⟨a,ha,haω⟩ := exists_plane_of_regular hω hreg
  have hdiv : canonicalDivisorOf (planeToField_ne_zero ha)=(2:ℕ) • B := by
    ext v
    rw [canonicalDivisorOf_apply,haω]
    have hh:=congrArg (fun D:ActualDivisor=>D v) hcan
    simpa only [canonicalDivisorOf_apply] using hh
  refine ⟨B,a,ha,hB,hcl,hdeg,hell,hdiv,huniq,?_⟩
  intro b hb hdivb
  obtain ⟨u,hu,huf⟩ := same_canonical_divisor_scalar ThetaDNativeSections.actual_constants
    (planeToField_ne_zero ha) (planeToField_ne_zero hb) (hdiv.trans hdivb.symm)
  refine ⟨u,hu,planeToField_injective ?_⟩
  rw [map_smul]
  exact huf.symm

#print axioms planeToField_injective
#print axioms exists_plane_of_regular
#print axioms odd_theta_unique_canonical_line
end FourCorner.ThetaOddThetaCanonicalLines
