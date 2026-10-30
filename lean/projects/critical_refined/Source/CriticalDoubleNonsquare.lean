import CriticalOriginalFieldEquiv
import CriticalEllipticBaseChange
import CriticalLiteralDouble

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 40000
namespace FourCorner.CriticalDoubleNonsquare
open CriticalRadicalField
variable (k : Type*) [Field k]

/-- The literal product obstruction, transported through the proved ORIGINAL
coordinate map, detects the nontrivial x squareclass on native E. -/
theorem elliptic_x_nonsquare_closed [IsAlgClosed k]
    (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    ¬IsSquare (CriticalEllipticField.x k) := by
  let e:=CriticalOriginalFieldEquiv.equiv k i hi h2
  let I:=algebraMap k (field k i) i
  have hI : I^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k (field k i)) hi
  have h2F : (2:field k i)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (field k i))).mpr h2
  have hq:=actual_critical_equations k i
  have hs:=CriticalFieldEquivalence.shift_nonzero (a_transcendental k i)
  have hh:=CriticalProductSquareclass.original_product_squareclass I (a k i) (b k i) (c k i)
    hI h2F hq.1 (by simpa only [map_add,map_one] using hq.2) hs
  intro hx
  have he : IsSquare (e (CriticalEllipticField.x k)) := hx.map e
  rw [CriticalOriginalFieldEquiv.equiv_x] at he
  have hp:=he.mul (IsSquare.sq (CriticalProductSquareclass.squareFactor I
    (CriticalConicParameter.parameter (a k i) (b k i)) (c k i)))
  rw [←hh] at hp
  exact CriticalProductNonsquare.literal_product_nonsquare i hi h2 hp

/-- Nonsquareness descends from the genuine algebraically closed native
model through an actual coordinate-preserving function-field embedding. -/
theorem elliptic_x_nonsquare (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    ¬IsSquare (CriticalEllipticField.x k) := by
  intro hx
  let L:=AlgebraicClosure k
  have hiL : (algebraMap k L i)^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k L) hi
  have h2L : (2:L)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k L)).mpr h2
  apply elliptic_x_nonsquare_closed L (algebraMap k L i) hiL h2L
  have h:=hx.map (CriticalEllipticBaseChange.map k L)
  simpa only [CriticalEllipticBaseChange.map_x] using h

/-- The original product radicand is nonsquare over EVERY allowed constant
field, not merely over algebraically closed fields. -/
theorem original_product_nonsquare (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    ¬IsSquare (2*(c k i+a k i*b k i)) := by
  let e:=CriticalOriginalFieldEquiv.equiv k i hi h2
  let I:=algebraMap k (field k i) i
  have hI : I^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k (field k i)) hi
  have h2F : (2:field k i)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (field k i))).mpr h2
  have hq:=actual_critical_equations k i
  have hs:=CriticalFieldEquivalence.shift_nonzero (a_transcendental k i)
  let g:=CriticalProductSquareclass.squareFactor I
    (CriticalConicParameter.parameter (a k i) (b k i)) (c k i)
  have hh : 2*(c k i+a k i*b k i)=e (CriticalEllipticField.x k)*g^2 := by
    rw [CriticalOriginalFieldEquiv.equiv_x]
    exact CriticalProductSquareclass.original_product_squareclass I (a k i) (b k i) (c k i)
      hI h2F hq.1 (by simpa only [map_add,map_one] using hq.2) hs
  have hrad : 2*(c k i+a k i*b k i)≠0 := CriticalLiteralDouble.radicand_ne_zero k i hi h2
  have hg : g≠0 := by intro hz; rw [hz,zero_pow (by decide),mul_zero] at hh; exact hrad hh
  intro h
  rw [hh] at h
  have hsq:=h.mul (IsSquare.sq g⁻¹)
  have he : (e (CriticalEllipticField.x k)*g^2)*(g⁻¹)^2=e (CriticalEllipticField.x k) := by
    field_simp [hg]
  rw [he] at hsq
  have hback:=hsq.map e.symm
  simp only [AlgEquiv.symm_apply_apply] at hback
  exact elliptic_x_nonsquare k i hi h2 hback

end FourCorner.CriticalDoubleNonsquare
#print axioms FourCorner.CriticalDoubleNonsquare.elliptic_x_nonsquare_closed
#print axioms FourCorner.CriticalDoubleNonsquare.elliptic_x_nonsquare
#print axioms FourCorner.CriticalDoubleNonsquare.original_product_nonsquare
