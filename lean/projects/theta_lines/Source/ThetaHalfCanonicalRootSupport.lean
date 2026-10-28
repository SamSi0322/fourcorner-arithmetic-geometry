import ThetaRootCanonicalSections

namespace FourCorner.ThetaHalfCanonicalRootSupport
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaLiteralBinaryRestrictions BinaryQuarticDoubleRoots
open ThetaProjectiveRootPlaceEmbedding ThetaRootCanonicalSections ThetaDCanonicalInfinityDivisor
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem root_half_order_positive (L : ThetaLine K) (B : Divisor K field)
    (hcan : canonicalDivisorOf (nonzero L)=(2:ℕ) • B) (P : Root L) : 0<B (rootPlace L P) := by
  have hp := root_positive L P
  have he := congrArg (fun C : Divisor K field=>C (rootPlace L P)) hcan
  simp only [canonicalDivisorOf_apply,Finsupp.smul_apply,nsmul_eq_mul] at he
  omega

/-- Effective degree two is exhausted by two distinct positive places.
The repeated-place possibility is included in the input and is eliminated
only by the actual distinct native roots and their injective Place images. -/
theorem two_positive_exhaust (B : Divisor K field) (hB : 0≤B) (hd : Divisor.degree B=2)
    (P Q : Place K field) (hne : P≠Q) (hp : 0<B P) (hq : 0<B Q) :
    B=Finsupp.single P 1+Finsupp.single Q 1 := by
  let E : Divisor K field := Finsupp.single P 1+Finsupp.single Q 1
  have hle : E≤B := by
    intro w
    change ((Finsupp.single P (1:ℤ)+Finsupp.single Q 1 : Divisor K field) w)≤B w
    by_cases hwP : w=P
    · subst w
      simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hne,add_zero]
      omega
    · by_cases hwQ : w=Q
      · subst w
        simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hne.symm,zero_add]
        omega
      · simpa only [Finsupp.add_apply,Finsupp.single_eq_of_ne hwP,Finsupp.single_eq_of_ne hwQ,zero_add,Finsupp.zero_apply] using hB w
  have he : Divisor.degree E=2 := by
    simp [E,map_add,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]
  have hz : Divisor.degree (B-E)=0 := by rw [map_sub,hd,he];norm_num
  exact sub_eq_zero.mp (divisor_zero_of_nonnegative_degree_zero _ (sub_nonneg.mpr hle) hz)

 theorem half_canonical_has_two_distinct_root_places (L : ThetaLine K)
    (B : Divisor K field) (hB : 0≤B) (hd : Divisor.degree B=2)
    (hcan : canonicalDivisorOf (nonzero L)=(2:ℕ) • B) :
    ∃P Q : Root L,P≠Q ∧ rootPlace L P≠rootPlace L Q ∧
      B=Finsupp.single (rootPlace L P) 1+Finsupp.single (rootPlace L Q) 1 := by
  obtain ⟨P,Q,hne,hP,hQ⟩ := ThetaRestrictionHasTwoRoots.two_projective_zeros L
  let p : Root L := ⟨P,hP⟩
  let q : Root L := ⟨Q,hQ⟩
  have hpq : p≠q := fun h=>hne (congrArg Subtype.val h)
  have hw := fun h=>hpq (rootPlace_injective L h)
  exact ⟨p,q,hpq,hw,two_positive_exhaust B hB hd _ _ hw
    (root_half_order_positive L B hcan p) (root_half_order_positive L B hcan q)⟩

#print axioms root_half_order_positive
#print axioms two_positive_exhaust
#print axioms half_canonical_has_two_distinct_root_places
end
end FourCorner.ThetaHalfCanonicalRootSupport
