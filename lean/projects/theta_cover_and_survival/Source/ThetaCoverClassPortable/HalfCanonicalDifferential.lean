import ThetaCoverClassPortable.PicEffectiveRepresentatives
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RatFuncPlaces

noncomputable section
set_option autoImplicit false
open AlgebraicCurve KaehlerDifferential
namespace FourCorner.DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K:=K) (F:=F)]
variable [∀v : Place K F,v.DCoordGenerates]

 theorem coeff_ne_zero {ω : Ω[F⁄K]} (hω : ω≠0) (v : Place K F) :
    v.differentialCoeff ω≠0 := by
  intro h
  have hh:=v.differentialCoeff_smul_dCoord ω
  rw [h,zero_smul] at hh
  exact hω hh.symm

 theorem canonical_smul_apply {f : F} (hf : f≠0) {ω : Ω[F⁄K]} (hω : ω≠0)
    (v : Place K F) :
    canonicalDivisorOf (smul_ne_zero hf hω) v=v.ord f+canonicalDivisorOf hω v := by
  rw [canonicalDivisorOf_apply,canonicalDivisorOf_apply]
  exact v.ordDifferential_smul hf (coeff_ne_zero hω v)

 theorem canonical_class_independent {ω η : Ω[F⁄K]} (hω : ω≠0) (hη : η≠0) :
    divisorClass (canonicalDivisorOf hω)=divisorClass (canonicalDivisorOf hη) := by
  obtain ⟨f,hf⟩ := exists_smul_eq_of_finrank_eq_one IsCurveOver.finrank_kaehler hη ω
  have hf0 : f≠0 := by
    intro hh
    rw [hh,zero_smul] at hf
    exact hω hf.symm
  apply (class_eq_iff_principal_sub _ _).mpr
  refine ⟨f,hf0,fun v=>?_⟩
  simp only [Finsupp.sub_apply,canonicalDivisorOf_apply]
  have hv : v.ordDifferential ω=v.ord f+v.ordDifferential η := by
    rw [←hf]
    exact v.ordDifferential_smul hf0 (coeff_ne_zero hη v)
  linarith

 theorem canonicalClass_eq {ω : Ω[F⁄K]} (hω : ω≠0) :
    canonicalClass K F=divisorClass (canonicalDivisorOf hω) := by
  unfold canonicalClass
  split_ifs with h
  · exact canonical_class_independent h.choose_spec hω
  · exact False.elim (h ⟨ω,hω⟩)

 theorem regular_of_canonical_effective {ω : Ω[F⁄K]} (hω : ω≠0)
    (h : 0≤canonicalDivisorOf hω) : ω∈regularDifferentials K F := by
  apply mem_regularDifferentials_iff.mpr
  intro v
  refine ⟨v.differentialCoeff ω,?_,(v.differentialCoeff_smul_dCoord ω).symm⟩
  apply v.mem_iff_adicValuation_le_one.mpr
  apply v.adicValuation_le_one_iff.mpr
  right
  have hv : (0:ℤ)≤canonicalDivisorOf hω v := h v
  rwa [canonicalDivisorOf_apply] at hv

/-- A genuine half-canonical divisor CLASS produces a nonzero actual rational
Kähler differential with EXACT all-place canonical divisor 2B. Effectivity
then proves regularity at every Place, including all infinity Places. -/
theorem half_canonical_effective_differential (B : Divisor K F) (hB : 0≤B)
    (hclass : (2:ℕ) • divisorClass B=canonicalClass K F) :
    ∃ (ω : Ω[F⁄K]) (hω : ω≠0),
      ω∈regularDifferentials K F ∧ canonicalDivisorOf hω=(2:ℕ) • B := by
  obtain ⟨η,hη⟩ := exists_ne (0:Ω[F⁄K])
  have hmk : divisorClass ((2:ℕ) • B)=divisorClass (canonicalDivisorOf hη) := by
    calc
      _=(2:ℕ) • divisorClass B := by simp only [two_nsmul];rfl
      _=canonicalClass K F := hclass
      _=_ := canonicalClass_eq hη
  obtain ⟨f,hf,hdiv⟩ := (class_eq_iff_principal_sub _ _).mp hmk
  let ω : Ω[F⁄K] := f • η
  have hω : ω≠0 := smul_ne_zero hf hη
  have heq : canonicalDivisorOf hω=(2:ℕ) • B := by
    ext v
    change canonicalDivisorOf (smul_ne_zero hf hη) v=_
    rw [canonical_smul_apply hf hη]
    have hh:=hdiv v
    simp only [Finsupp.sub_apply] at hh
    linarith
  refine ⟨ω,hω,regular_of_canonical_effective hω ?_,heq⟩
  rw [heq,two_nsmul]
  exact add_nonneg hB hB

/-- Odd theta is an intrinsic class of the TRUE divisor Picard quotient.
No represented Jacobian, line-bundle designation, or dimension flag occurs. -/
def IsOddThetaClass (c : Pic K F) : Prop :=
  (2:ℕ) • c=canonicalClass K F ∧ Odd (picEll c)

#print axioms canonical_class_independent
#print axioms canonicalClass_eq
#print axioms half_canonical_effective_differential
end FourCorner.DivisorPicClassification
