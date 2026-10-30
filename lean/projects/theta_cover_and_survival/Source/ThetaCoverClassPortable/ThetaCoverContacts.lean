import ThetaCoverClassPortable.ThetaCoverFunctions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ThetaCoverContacts
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaCoverFunctions
open ThetaActualLineDifferentials ThetaActualHalfCanonicalContacts ThetaContactOddness
open ThetaRootCanonicalSections ThetaGaloisCanonicalCorrespondence ThetaOddNativeSquareContact
open ThetaDActualDifferential ThetaDNaturalGlobalDifferentials DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : Module K Γ(toBase.kaehler,⊤) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

abbrev r : K := ThetaLinesAbsoluteGalois.r
abbrev alphaPlus : K := -r/2
abbrev alphaMinus : K := r/2

theorem r_ne_zero : r≠0 := by
  intro hr
  have hh:=ThetaLinesAbsoluteGalois.r_sq
  change r^2=2 at hh
  rw [hr,zero_pow (by decide)] at hh
  norm_num at hh

theorem plus_square_contact : IsThetaSquareContact (.affine alphaPlus 0) := by
  apply (theta_no_hyperflex _).mpr
  apply (theta_affine_x_axis_bitangent_iff _).mpr
  left
  dsimp [alphaPlus]
  rw [div_pow,neg_sq,ThetaLinesAbsoluteGalois.r_sq]
  norm_num

theorem minus_square_contact : IsThetaSquareContact (.affine alphaMinus 0) := by
  apply (theta_no_hyperflex _).mpr
  apply (theta_affine_x_axis_bitangent_iff _).mpr
  left
  dsimp [alphaMinus]
  rw [div_pow,ThetaLinesAbsoluteGalois.r_sq]
  norm_num

/-- Actual two-point contact data from native geometry for ell+=Z+X/sqrt2. -/
def plusData : ContactData (affineGlobalSection alphaPlus 0) :=
  Classical.choice (affine_contact_data alphaPlus 0 plus_square_contact)
/-- Actual two-point contact data for ell-=Z-X/sqrt2. -/
def minusData : ContactData (affineGlobalSection alphaMinus 0) :=
  Classical.choice (affine_contact_data alphaMinus 0 minus_square_contact)

def Bplus : Divisor K field := plusData.divisor
def Bminus : Divisor K field := minusData.divisor

 theorem plus_effective : 0≤Bplus := plusData.effective
 theorem minus_effective : 0≤Bminus := minusData.effective
 theorem plus_ell_one : ell Bplus=1 := affine_contact_ell_one _ _ plus_square_contact plusData
 theorem minus_ell_one : ell Bminus=1 := affine_contact_ell_one _ _ minus_square_contact minusData
 theorem plus_degree : Divisor.degree Bplus=2 := plusData.degree_two
 theorem minus_degree : Divisor.degree Bminus=2 := minusData.degree_two

 theorem radical_inv : radical⁻¹=radical/2 := by
  apply (eq_div_iff (show (2:field)≠0 by norm_num)).mpr
  apply (mul_left_cancel₀ radical_ne_zero)
  rw [←mul_assoc,mul_inv_cancel₀ radical_ne_zero,one_mul,←pow_two,radical_sq]

 theorem plus_germ : genericGerm (affineGlobalSection alphaPlus 0)=ellPlus • omega := by
  rw [affineGlobalSection_germ,smul_smul,affineFunction_times_y]
  congr 1
  rw [map_zero,zero_mul,sub_zero]
  change 1-algebraMap K field (-r/2)*x=ellPlus
  rw [map_div₀,map_neg,map_ofNat]
  change 1-(-radical/2)*x=ellPlus
  unfold ellPlus
  simp only [div_eq_mul_inv]
  rw [radical_inv]
  ring

 theorem minus_germ : genericGerm (affineGlobalSection alphaMinus 0)=ellMinus • omega := by
  rw [affineGlobalSection_germ,smul_smul,affineFunction_times_y]
  congr 1
  rw [map_zero,zero_mul,sub_zero]
  change 1-algebraMap K field (r/2)*x=ellMinus
  rw [map_div₀,map_ofNat]
  change 1-(radical/2)*x=ellMinus
  unfold ellMinus
  simp only [div_eq_mul_inv]
  rw [radical_inv]
  ring

 theorem plus_ord (w : Place K field) :
    w.ord ellPlus+ThetaDCanonicalInfinityDivisor.infinitySum w=2*Bplus w := by
  have hh:=congrArg (fun D : Divisor K field=>D w) plusData.doubled_divisor
  rw [canonicalDivisorOf_apply,plus_germ,
    w.ordDifferential_smul ellPlus_ne_zero (ThetaDGlobalCanonicalCandidate.coefficient_nonzero w)] at hh
  have hH : w.ordDifferential omega=ThetaDCanonicalInfinityDivisor.infinitySum w := by
    rw [←canonicalDivisorOf_apply omega_ne_zero,ThetaDCanonicalInfinityDivisor.canonical_divisor_exact]
  rw [hH] at hh
  simpa only [Bplus,ContactData.divisor,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] using hh

 theorem minus_ord (w : Place K field) :
    w.ord ellMinus+ThetaDCanonicalInfinityDivisor.infinitySum w=2*Bminus w := by
  have hh:=congrArg (fun D : Divisor K field=>D w) minusData.doubled_divisor
  rw [canonicalDivisorOf_apply,minus_germ,
    w.ordDifferential_smul ellMinus_ne_zero (ThetaDGlobalCanonicalCandidate.coefficient_nonzero w)] at hh
  have hH : w.ordDifferential omega=ThetaDCanonicalInfinityDivisor.infinitySum w := by
    rw [←canonicalDivisorOf_apply omega_ne_zero,ThetaDCanonicalInfinityDivisor.canonical_divisor_exact]
  rw [hH] at hh
  simpa only [Bminus,ContactData.divisor,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] using hh

/-- Nontriviality is derived from uniqueness of actual effective odd-theta
representatives and scalar comparison of actual canonical sections. -/
theorem contact_class_difference_ne_zero : divisorClass (Bplus-Bminus)≠0 := by
  intro hz
  have hcl : divisorClass Bminus=divisorClass Bplus := by
    change divisorClass Bplus-divisorClass Bminus=0 at hz
    exact (sub_eq_zero.mp hz).symm
  have hc := affine_contact_odd alphaPlus 0 plus_square_contact plusData
  have hp : CanonicalRepresentative (divisorClass Bplus) Bplus
      (ThetaRootCanonicalSections.coefficients (.affine alphaPlus 0)) :=
    ⟨coefficients_ne_zero _,plus_effective,rfl,plusData.doubled_divisor⟩
  have hm : CanonicalRepresentative (divisorClass Bplus) Bminus
      (ThetaRootCanonicalSections.coefficients (.affine alphaMinus 0)) :=
    ⟨coefficients_ne_zero _,minus_effective,hcl,minusData.doubled_divisor⟩
  obtain ⟨_,u,_,hu⟩ := representative_unique hc hp hm
  have hu1 : u=1 := by
    have hh:=congrFun hu 2
    change (1:K)=u*1 at hh
    simpa only [mul_one] using hh.symm
  have hh:=congrFun hu 0
  change -alphaMinus=u*(-alphaPlus) at hh
  rw [hu1,one_mul] at hh
  dsimp [alphaPlus,alphaMinus] at hh
  have hr : r=0 := by linear_combination -hh
  exact r_ne_zero hr

 theorem contact_divisors_distinct : Bplus≠Bminus := by
  intro he
  apply contact_class_difference_ne_zero
  rw [he,sub_self]
  rfl

#print axioms contact_class_difference_ne_zero
end FourCorner.ThetaCoverContacts
