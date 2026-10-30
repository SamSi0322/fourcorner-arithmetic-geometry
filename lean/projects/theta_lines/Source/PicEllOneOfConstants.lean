import HalfCanonicalDifferential

noncomputable section
set_option autoImplicit false
open AlgebraicCurve KaehlerDifferential
namespace FourCorner.DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The forward contact worker's exact all-g constant-sections output is
sufficient: no dimension-one or odd-theta conclusion is an input. -/
theorem ell_eq_one_of_constant_sections (B : Divisor K F) (hB : 0≤B)
    (h : ∀g : F,g∈LSpace B → ∃c : K,algebraMap K F c=g) : ell B=1 := by
  have heq : LSpace B=LinearMap.range (Algebra.linearMap K F) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨c,hc⟩ := h g hg
      exact ⟨c,hc⟩
    · rintro g ⟨c,rfl⟩
      exact lSpace_mono hB (algebraMap_mem_lSpace_zero c)
  rw [ell,heq,LinearMap.finrank_range_of_inj (f:=Algebra.linearMap K F)
    (algebraMap K F).injective,Module.finrank_self]

 theorem constant_sections_of_smul_condition (B : Divisor K F)
    {η : Ω[F⁄K]} (hη : η≠0)
    (h : ∀g : F,g∈LSpace B → ∃c : K,g • η=c • η) :
    ∀g : F,g∈LSpace B → ∃c : K,algebraMap K F c=g := by
  intro g hg
  obtain ⟨c,hc⟩ := h g hg
  refine ⟨c,?_⟩
  have hz : (g-algebraMap K F c) • η=0 := by
    rw [sub_smul,algebraMap_smul,hc,sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hη)).symm

variable [IsCurveOver K F] [HasCanonicalDivisor (K:=K) (F:=F)]
variable [∀v : Place K F,v.DCoordGenerates]

/-- Full genuine divisor-Pic forward assembly from the actual contact
form's exact double divisor and the proved all-g constants criterion.
No contact/odd/Pic identification is inserted as an assumption. -/
theorem isOddThetaClass_of_constant_sections (B : Divisor K F) (hB : 0≤B)
    {η : Ω[F⁄K]} (hη : η≠0) (hcan : canonicalDivisorOf hη=(2:ℕ) • B)
    (h : ∀g : F,g∈LSpace B → ∃c : K,algebraMap K F c=g) :
    IsOddThetaClass (divisorClass B) := by
  constructor
  · calc
      (2:ℕ) • divisorClass B=divisorClass ((2:ℕ) • B) := by simp only [two_nsmul];rfl
      _=divisorClass (canonicalDivisorOf hη) := by rw [hcan]
      _=canonicalClass K F := (canonicalClass_eq hη).symm
  · rw [picEll_class,ell_eq_one_of_constant_sections B hB h]
    decide

 theorem isOddThetaClass_of_smul_condition (B : Divisor K F) (hB : 0≤B)
    {η : Ω[F⁄K]} (hη : η≠0) (hcan : canonicalDivisorOf hη=(2:ℕ) • B)
    (h : ∀g : F,g∈LSpace B → ∃c : K,g • η=c • η) :
    IsOddThetaClass (divisorClass B) :=
  isOddThetaClass_of_constant_sections B hB hη hcan
    (constant_sections_of_smul_condition B hη h)

#print axioms ell_eq_one_of_constant_sections
#print axioms isOddThetaClass_of_constant_sections
end FourCorner.DivisorPicClassification
