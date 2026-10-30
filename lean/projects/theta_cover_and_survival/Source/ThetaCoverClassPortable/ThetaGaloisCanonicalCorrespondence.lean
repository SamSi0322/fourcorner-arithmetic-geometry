import ThetaCoverClassPortable.ThetaGaloisCanonicalPlane

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve KaehlerDifferential
namespace FourCorner.ThetaGaloisCanonicalCorrespondence
open ThetaDGeometricModel ThetaGaloisSchemeField ThetaGaloisFieldAction ThetaGaloisCanonicalPlane
open ThetaOddThetaCanonicalLines ThetaActualOddThetaClasses DivisorPicClassification SemilinearPicAndEll
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

/-- A TRUE canonical representative relation: actual divisor, actual Pic
class, original coefficient triple and exact actual Kähler divisor. -/
def CanonicalRepresentative (c : ActualPic) (B : ActualDivisor) (a : Fin 3→K) : Prop :=
  ∃ha : a≠0,0≤B ∧ divisorClass B=c ∧
    canonicalDivisorOf (planeToField_ne_zero ha)=(2:ℕ) • B

 theorem exists_representative (c : ActualPic) (hc : IsOddThetaClass c) :
    ∃B a,CanonicalRepresentative c B a ∧ Divisor.degree B=2 ∧ ell B=1 := by
  obtain ⟨B,a,ha,hB,hcl,hdeg,hell,hcan,-,-⟩ := odd_theta_unique_canonical_line c hc
  exact ⟨B,a,⟨ha,hB,hcl,hcan⟩,hdeg,hell⟩

 theorem representative_unique {c : ActualPic} (hc : IsOddThetaClass c)
    {B E : ActualDivisor} {a b : Fin 3→K}
    (hA : CanonicalRepresentative c B a) (hC : CanonicalRepresentative c E b) :
    E=B ∧ ∃u : K,u≠0 ∧ b=u • a := by
  obtain ⟨ha,hB,hBc,hcanA⟩ := hA
  obtain ⟨hb,hE,hEc,hcanC⟩ := hC
  obtain ⟨F,hF,hFc,-,-,hFU,-⟩ := actual_odd_theta_effective_unique c hc
  have hEB : E=B := (hFU E hE hEc).trans (hFU B hB hBc).symm
  have hforms : canonicalDivisorOf (planeToField_ne_zero ha)=
      canonicalDivisorOf (planeToField_ne_zero hb) := by
    rw [hcanA,hcanC,hEB]
  obtain ⟨u,hu,huf⟩ := same_canonical_divisor_scalar ThetaDNativeSections.actual_constants
    (planeToField_ne_zero ha) (planeToField_ne_zero hb) hforms
  refine ⟨hEB,u,hu,planeToField_injective ?_⟩
  rw [map_smul]
  exact huf.symm

 theorem representative_transport (σ : Gal) {c : ActualPic} {B : ActualDivisor} {a : Fin 3→K}
    (hA : CanonicalRepresentative c B a) :
    CanonicalRepresentative (picMap σ c) (absoluteAction σ • B) (coefficientMap σ a) := by
  obtain ⟨ha,hB,hBc,hcan⟩ := hA
  refine ⟨coefficientMap_ne_zero σ ha,smul_effective _ hB,?_,?_⟩
  · rw [←pic_smul_class,hBc]
    rfl
  · calc
      _=absoluteAction σ • canonicalDivisorOf (planeToField_ne_zero ha) :=
        canonical_plane_divisor_transport σ ha
      _=absoluteAction σ • ((2:ℕ) • B) := congrArg (fun E:ActualDivisor=>absoluteAction σ • E) hcan
      _=(2:ℕ) • (absoluteAction σ • B) := by simp only [two_nsmul,smul_add]

/-- EVERY choice of reverse representatives is equivariant in the actual
Pic action and the exact nonzero-scalar relation on original plane forms. -/
theorem reverse_classification_equivariant (σ : Gal) {c : ActualPic} (hc : IsOddThetaClass c)
    {B E : ActualDivisor} {a b : Fin 3→K}
    (hA : CanonicalRepresentative c B a)
    (hC : CanonicalRepresentative (picMap σ c) E b) :
    E=absoluteAction σ • B ∧ ∃u : K,u≠0 ∧ b=u • coefficientMap σ a :=
  representative_unique (picMap_odd σ hc) (representative_transport σ hA) hC

/-- Closed actual bridge: no presumed Pic/line correspondence, generation,
point-place equivariance or Galois action is supplied as a premise. -/
theorem actual_absolute_galois_reverse_bridge (σ : Gal) (c : ActualPic) (hc : IsOddThetaClass c) :
    ∃B a,CanonicalRepresentative c B a ∧ Divisor.degree B=2 ∧ ell B=1 ∧
      CanonicalRepresentative (picMap σ c) (absoluteAction σ • B) (coefficientMap σ a) ∧
      ∀E b,CanonicalRepresentative (picMap σ c) E b →
        E=absoluteAction σ • B ∧ ∃u : K,u≠0 ∧ b=u • coefficientMap σ a := by
  obtain ⟨B,a,hA,hdeg,hell⟩ := exists_representative c hc
  exact ⟨B,a,hA,hdeg,hell,representative_transport σ hA,
    fun E b hC=>reverse_classification_equivariant σ hc hA hC⟩

#print axioms representative_transport
#print axioms reverse_classification_equivariant
#print axioms actual_absolute_galois_reverse_bridge
end FourCorner.ThetaGaloisCanonicalCorrespondence
