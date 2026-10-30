import CriticalOriginalFieldEquiv
import CriticalDoubleFieldMap
import CriticalLiteralDouble

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalDoubleProductBridge
open CriticalRadicalField
variable (k : Type*) [Field k]

def factor (i : k) : field k i :=
  CriticalProductSquareclass.squareFactor (algebraMap k (field k i) i)
    (CriticalConicParameter.parameter (a k i) (b k i)) (c k i)

theorem radicand_factor (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    CriticalLiteralDouble.radicand k i=
      CriticalOriginalFieldEquiv.equiv k i hi h2 (CriticalEllipticField.x k)*factor k i^2 := by
  rw [CriticalOriginalFieldEquiv.equiv_x]
  apply CriticalProductSquareclass.original_product_squareclass
  · simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k (field k i)) hi
  · simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (field k i))).mpr h2
  · exact (actual_critical_equations k i).1
  · simpa only [map_add,map_one] using (actual_critical_equations k i).2
  · exact CriticalFieldEquivalence.shift_nonzero (a_transcendental k i)

theorem factor_nonzero (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) : factor k i≠0 := by
  intro h
  have hh:=radicand_factor k i hi h2
  rw [h,zero_pow (by decide),mul_zero] at hh
  exact CriticalLiteralDouble.radicand_ne_zero k i hi h2 hh

def baseMap (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    field k i →ₐ[k] CriticalEllipticField.field k :=
  (CriticalDoubleFieldMap.map k i hi h2).comp (CriticalOriginalFieldEquiv.equiv k i hi h2).symm.toAlgHom

def rootValue (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) : CriticalEllipticField.field k :=
  CriticalDoubleCM.rootX (algebraMap k (CriticalEllipticField.field k) i)
    (CriticalEllipticField.x k) (CriticalEllipticField.y k) *
      baseMap k i hi h2 (factor k i)

/-- The image of the ORIGINAL normalized product radicand under the genuine
base field embedding is the square of the displayed actual E function. -/
theorem rootValue_square (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    rootValue k i hi h2^2=baseMap k i hi h2 (CriticalLiteralDouble.radicand k i) := by
  rw [radicand_factor k i hi h2,map_mul,map_pow]
  have he : baseMap k i hi h2 (CriticalOriginalFieldEquiv.equiv k i hi h2 (CriticalEllipticField.x k))=
      CriticalDoubleFieldMap.map k i hi h2 (CriticalEllipticField.x k) := by
    change (CriticalDoubleFieldMap.map k i hi h2)
      ((CriticalOriginalFieldEquiv.equiv k i hi h2).symm
        ((CriticalOriginalFieldEquiv.equiv k i hi h2) (CriticalEllipticField.x k))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [he,←CriticalDoubleFieldMap.root_square k i hi h2]
  exact mul_pow _ _ 2

end FourCorner.CriticalDoubleProductBridge
#print axioms FourCorner.CriticalDoubleProductBridge.radicand_factor
#print axioms FourCorner.CriticalDoubleProductBridge.factor_nonzero
#print axioms FourCorner.CriticalDoubleProductBridge.baseMap
#print axioms FourCorner.CriticalDoubleProductBridge.rootValue_square
