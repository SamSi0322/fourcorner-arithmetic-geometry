import CriticalProjectiveResidues

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace FourCorner.CriticalOffBoundaryUnit
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalProjectiveResidues
variable {k:Type*} [Field k]
local instance relative (i:k) : Algebra (field k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (field k i) (CriticalLiteralDouble.field k i) := (relative i).toModule

lemma finite_f_order (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:0≤v.ord (a k i)) (hb:¬0<v.ord (CriticalBoundaryResidues.shift i)) :
    v.ord (CriticalProductValuation.f i)=0 := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hff:=CriticalProductValuation.nonzero i hi h2
  have hm:=CriticalProductValuation.integral_of_nonnegative i v hi h2 ha
  have hmem:a k i^2-1∈v.toValuationSubring :=
    v.toValuationSubring.sub_mem
      (v.toValuationSubring.pow_mem (regularA i hi h2 v ha).property 2) v.toValuationSubring.one_mem
  have htN:0≤v.ord (a k i^2-1) := (v.mem_iff_ord_nonneg hn.2.2.2).mp hmem
  have ht0:v.ord (a k i^2-1)=0 := by change ¬0<v.ord (a k i^2-1) at hb;omega
  have hi0:algebraMap k (field k i) i≠0 := (_root_.map_ne_zero _).mpr (CriticalElliptic23.iota_nonzero i hi)
  have he:=congrArg v.ord (CriticalProductValuation.product_identity i)
  rw [v.ord_mul hff.1 hff.2,v.ord_mul (neg_ne_zero.mpr hi0) (pow_ne_zero 2 hn.2.2.2),
    OddFifthUnramified.ord_neg,v.ord_algebraMap,CriticalProductValuation.square_order i v _,ht0] at he
  omega

/-- Off the ORIGINAL b=0 locus, EVERY actual rational place has a primitive
unit equation for the SAME cover. Its residue is precisely2f on its original
projective representative, including all V0-pole points and zero coordinates. -/
theorem off_boundary_unit (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational)
    (hb:¬0<v.ord (CriticalBoundaryResidues.shift i)) :
    ∃ u:v.toValuationSubring, IsUnit u ∧ ∃ r:CriticalLiteralDouble.field k i,
      r^2=algebraMap (field k i) (CriticalLiteralDouble.field k i) (u:field k i) ∧
      Algebra.adjoin (field k i) {r}=⊤ ∧
      evaluate v hv u=2*CriticalProjectiveCharacter.product (vector i hi h2 v hv) := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hff:=CriticalProductValuation.nonzero i hi h2
  have h2F:(2:field k i)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (field k i))).mpr h2
  have h2ord:v.ord (2:field k i)=0 := by simpa only [map_ofNat] using v.ord_algebraMap (2:k)
  by_cases ha:0≤v.ord (a k i)
  · let aa:=regularA i hi h2 v ha
    let bb:=regularB i hi h2 v ha
    let cc:=regularC i hi h2 v ha
    let u:v.toValuationSubring:=2*(cc+aa*bb)
    have hu0:(u:field k i)≠0 := CriticalLiteralDouble.radicand_ne_zero k i hi h2
    have huord:v.ord (u:field k i)=0 := by
      change v.ord (2*CriticalProductValuation.f i)=0
      rw [v.ord_mul h2F hff.1,h2ord,zero_add,finite_f_order i hi h2 v ha hb]
    have hunit:IsUnit u := ResidueValuationFacts.unit_of_ord_zero v u hu0 huord
    refine ⟨u,hunit,CriticalLiteralDouble.root k i,CriticalLiteralDouble.root_square k i,
      CriticalLiteralDouble.root_generates k i,?_⟩
    simp [u,aa,bb,cc,vector,ha,finiteVector,CriticalProjectiveCharacter.product,map_ofNat]
  · have han:v.ord (a k i)<0 := by omega
    let zz:=poleZero i hi h2 v han
    let bb:=poleB i hi h2 v han
    let cc:=poleC i hi h2 v han
    let u:v.toValuationSubring:=2*(zz*cc+bb)
    have huval:(u:field k i)=CriticalLiteralDouble.radicand k i/a k i^2 := by
      change 2*((a k i)⁻¹*(c k i/a k i)+b k i/a k i)=2*(c k i+a k i*b k i)/a k i^2
      field_simp [hn.1] <;> ring
    have hu0:(u:field k i)≠0 := by rw [huval];exact div_ne_zero (CriticalLiteralDouble.radicand_ne_zero k i hi h2) (pow_ne_zero 2 hn.1)
    have hrord:v.ord (CriticalLiteralDouble.radicand k i)=2*v.ord (a k i) := by
      change v.ord (2*CriticalProductValuation.f i)=_
      rw [v.ord_mul h2F hff.1,h2ord,zero_add,CriticalProductOrders.negative_a i hi h2 v han]
    have huord:v.ord (u:field k i)=0 := by
      rw [huval,QuadraticRescaledUnit.ord_div v (CriticalLiteralDouble.radicand_ne_zero k i hi h2)
        (pow_ne_zero 2 hn.1),hrord,CriticalProductValuation.square_order i v _]
      ring
    have hunit:IsUnit u := ResidueValuationFacts.unit_of_ord_zero v u hu0 huord
    refine ⟨u,hunit,CriticalLiteralDouble.root k i/algebraMap (field k i) (CriticalLiteralDouble.field k i) (a k i),?_,
      QuadraticRescaledUnit.adjoin_div_algebraMap_eq_top (CriticalLiteralDouble.root k i) hn.1
        (CriticalLiteralDouble.root_generates k i),?_⟩
    · rw [div_pow,CriticalLiteralDouble.root_square,←map_pow,←map_div₀]
      exact congrArg (algebraMap (field k i) (CriticalLiteralDouble.field k i)) huval.symm
    · simp [u,zz,bb,cc,vector,ha,poleVector,CriticalProjectiveCharacter.product,map_ofNat]

end FourCorner.CriticalOffBoundaryUnit
#print axioms FourCorner.CriticalOffBoundaryUnit.finite_f_order
#print axioms FourCorner.CriticalOffBoundaryUnit.off_boundary_unit
