import ThetaVerticalContactOrder

namespace FourCorner.ThetaContactDifferentialDivisors
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDActualDifferential
open ThetaRegularFunctionDifferential ThetaDGlobalCanonicalCandidate ThetaDPlaneRegularForms
open ThetaGeometricContactPoints ThetaActualLineDifferentials ThetaContactTangencyCertificates
open ThetaAffineContactOrder ThetaVerticalContactOrder ThetaDCanonicalInfinityDivisor
open ThetaDNaturalGlobalDifferentials
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

/-- These are the TRUE generic germs of the ACTUAL global original line
sections constructed through the NEW natural sheaf comparison. -/
def affineDifferential (α β : K) : Ω[field⁄K] := genericGerm (affineGlobalSection α β)
def verticalDifferential (t : K) : Ω[field⁄K] := genericGerm (verticalGlobalSection t)

 theorem affineDifferential_ne_zero (α β : K) : affineDifferential α β≠0 := by
  rw [affineDifferential,affineGlobalSection_germ]
  exact smul_ne_zero (affineFunction_ne_zero α β) (smul_ne_zero ThetaActualLineDifferentials.y_ne_zero omega_ne_zero)

 theorem verticalDifferential_ne_zero (t : K) : verticalDifferential t≠0 := by
  rw [verticalDifferential,verticalGlobalSection_germ]
  exact smul_ne_zero (verticalFunction_ne_zero t) omega_ne_zero

 theorem germ_regular (s : Γ(toBase.kaehler,⊤)) : genericGerm s∈regularDifferentials K field := by
  rw [←globalRegularEquiv_germ]
  exact (globalRegularEquiv s).property

 theorem coefficient_regular_of_regular {η : Ω[field⁄K]} (hη : η∈regularDifferentials K field) (w : Place K field) :
    coefficient w η∈w.toValuationSubring := by
  obtain ⟨f,hf,he⟩ := hη w
  have hh : coefficient w η=f := by
    change w.differentialCoeff η=f
    rw [he,w.differentialCoeff_smul,w.differentialCoeff_dCoord,mul_one]
  rw [hh]
  exact hf

 theorem coefficient_ne_zero {η : Ω[field⁄K]} (hη : η≠0) (w : Place K field) : coefficient w η≠0 := by
  intro hz
  have hh := w.differentialCoeff_smul_dCoord η
  change coefficient w η • w.dCoord=η at hh
  rw [hz,zero_smul] at hh
  exact hη hh.symm

 theorem germ_orders_nonnegative (s : Γ(toBase.kaehler,⊤)) (w : Place K field) :
    0≤w.ordDifferential (genericGerm s) :=
  w.ord_nonneg_of_mem (coefficient_regular_of_regular (germ_regular s) w)

 theorem affine_differential_contact_order (α β z : K) (hz : thetaF z 1 (α*z+β)=0)
    (hd : (ThetaLinesPolynomialContacts.affineRestriction α β).derivative.eval z=0) :
    2≤(affinePlace α β z hz).ordDifferential (affineDifferential α β) := by
  let w := affinePlace α β z hz
  have hl := affine_function_order_ge_two α β z hz hd
  change 2≤w.ord (affineFunction α β) at hl
  have hb : 0≤w.ordDifferential (y • omega) := w.ord_nonneg_of_mem (yomega_coefficient_regular w)
  have hn : y • omega≠0 := smul_ne_zero ThetaActualLineDifferentials.y_ne_zero omega_ne_zero
  have he : w.ordDifferential (affineDifferential α β)=w.ord (affineFunction α β)+w.ordDifferential (y • omega) := by
    rw [affineDifferential,affineGlobalSection_germ]
    exact w.ordDifferential_smul (affineFunction_ne_zero α β) (coefficient_ne_zero hn w)
  change 2≤w.ordDifferential (affineDifferential α β)
  omega

 theorem vertical_differential_contact_order (t z : K) (hz : thetaF (t*z) z 1=0)
    (hd : (ThetaLinesPolynomialContacts.verticalRestriction t).derivative.eval z=0) :
    2≤(verticalPlace t z hz).ordDifferential (verticalDifferential t) := by
  let w := verticalPlace t z hz
  have hl := vertical_function_order_ge_two t z hz hd
  change 2≤w.ord (verticalFunction t) at hl
  have hb : 0≤w.ordDifferential omega := all_orders_nonnegative w
  have he : w.ordDifferential (verticalDifferential t)=w.ord (verticalFunction t)+w.ordDifferential omega := by
    rw [verticalDifferential,verticalGlobalSection_germ]
    exact w.ordDifferential_smul (verticalFunction_ne_zero t) (coefficient_ne_zero omega_ne_zero w)
  change 2≤w.ordDifferential (verticalDifferential t)
  omega

/-- Actual degree-four canonical geometry forces two genuine double zeros
and excludes every other place. This is NOT a restriction-polynomial label. -/
theorem canonical_two_double_zeros {η : Ω[field⁄K]} (hη : η≠0)
    (hreg : ∀w : Place K field,0≤w.ordDifferential η)
    (P Q : Place K field) (hpq : P≠Q)
    (hP : 2≤P.ordDifferential η) (hQ : 2≤Q.ordDifferential η) :
    canonicalDivisorOf hη=Finsupp.single P 2+Finsupp.single Q 2 := by
  let B : Divisor K field := Finsupp.single P 2+Finsupp.single Q 2
  have hB (w : Place K field) : B w=(if w=P then 2 else 0)+(if w=Q then 2 else 0) := by
    simp only [B,Finsupp.add_apply,Finsupp.single_apply,eq_comm]
  have hle : B≤canonicalDivisorOf hη := by
    intro w
    rw [hB,canonicalDivisorOf_apply]
    by_cases hwP : w=P
    · subst w;simpa [hpq] using hP
    · by_cases hwQ : w=Q
      · subst w;simpa [hpq.symm] using hQ
      · simpa only [if_neg hwP,if_neg hwQ,zero_add] using hreg w
  have hd : Divisor.degree B=4 := by
    simp [B,map_add,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]
  have hz : Divisor.degree (canonicalDivisorOf hη-B)=0 := by
    rw [map_sub,ThetaDNativeSections.canonical_degree_four hη,hd]
    norm_num
  exact sub_eq_zero.mp (divisor_zero_of_nonnegative_degree_zero _ (sub_nonneg.mpr hle) hz)

/-- Every broad square-contact affine line gives an ACTUAL half-canonical
contact divisor on the original geometric curve, with two DISTINCT actual
point-places and exact order two at each, and no other zeros. -/
theorem affine_contact_divisor (α β : K) (h : IsThetaSquareContact (.affine α β)) :
    ∃x y : K,∃hx : thetaF x 1 (α*x+β)=0,∃hy : thetaF y 1 (α*y+β)=0,
      x≠y ∧ affinePlace α β x hx≠affinePlace α β y hy ∧
      canonicalDivisorOf (affineDifferential_ne_zero α β)=
        Finsupp.single (affinePlace α β x hx) 2+Finsupp.single (affinePlace α β y hy) 2 := by
  obtain ⟨c,x,y,hx,hy,hc,hxy,hpq,hf,_,_⟩ := affine_contacts α β h
  have hdx : (ThetaLinesPolynomialContacts.affineRestriction α β).derivative.eval x=0 := by
    rw [hf];exact factored_derivative_zero c x y
  have hdy : (ThetaLinesPolynomialContacts.affineRestriction α β).derivative.eval y=0 := by
    have he : ThetaLinesPolynomialContacts.affineRestriction α β=
        Polynomial.C c*(Polynomial.X-Polynomial.C y)^2*(Polynomial.X-Polynomial.C x)^2 := by rw [hf];ring
    rw [he];exact factored_derivative_zero c y x
  refine ⟨x,y,hx,hy,hxy,hpq,?_⟩
  exact canonical_two_double_zeros (affineDifferential_ne_zero α β)
    (germ_orders_nonnegative (affineGlobalSection α β)) _ _ hpq
    (affine_differential_contact_order α β x hx hdx) (affine_differential_contact_order α β y hy hdy)

 theorem vertical_contact_divisor (t : K) (h : IsThetaSquareContact (.vertical t)) :
    ∃x y : K,∃hx : thetaF (t*x) x 1=0,∃hy : thetaF (t*y) y 1=0,
      x≠y ∧ verticalPlace t x hx≠verticalPlace t y hy ∧
      canonicalDivisorOf (verticalDifferential_ne_zero t)=
        Finsupp.single (verticalPlace t x hx) 2+Finsupp.single (verticalPlace t y hy) 2 := by
  obtain ⟨c,x,y,hx,hy,hc,hxy,hpq,hf,_,_⟩ := vertical_contacts t h
  have hdx : (ThetaLinesPolynomialContacts.verticalRestriction t).derivative.eval x=0 := by
    rw [hf];exact factored_derivative_zero c x y
  have hdy : (ThetaLinesPolynomialContacts.verticalRestriction t).derivative.eval y=0 := by
    have he : ThetaLinesPolynomialContacts.verticalRestriction t=
        Polynomial.C c*(Polynomial.X-Polynomial.C y)^2*(Polynomial.X-Polynomial.C x)^2 := by rw [hf];ring
    rw [he];exact factored_derivative_zero c y x
  refine ⟨x,y,hx,hy,hxy,hpq,?_⟩
  exact canonical_two_double_zeros (verticalDifferential_ne_zero t)
    (germ_orders_nonnegative (verticalGlobalSection t)) _ _ hpq
    (vertical_differential_contact_order t x hx hdx) (vertical_differential_contact_order t y hy hdy)

#print axioms affine_differential_contact_order
#print axioms vertical_differential_contact_order
#print axioms canonical_two_double_zeros
#print axioms affine_contact_divisor
#print axioms vertical_contact_divisor
end
end FourCorner.ThetaContactDifferentialDivisors
