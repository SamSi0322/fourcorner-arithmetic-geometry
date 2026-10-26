import CriticalDoubleCM
import CriticalEllipticEvaluation
import CriticalFieldEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace FourCorner.CriticalDoubleFieldMap
open CriticalEllipticField CriticalDoubleCM
variable (k : Type*) [Field k]

theorem x_nonzero : x k≠0 := by
  intro h
  apply x_transcendental k
  rw [h]
  exact isAlgebraic_zero

theorem y_nonzero : y k≠0 := by
  intro h
  have he:=CriticalEllipticField.equation k
  have hs := CriticalFieldEquivalence.shift_nonzero (x_transcendental k)
  have hh : x k*(x k^2-1) = 0 := by rw [h] at he; linear_combination -he
  exact (mul_ne_zero (x_nonzero k) hs) hh

def map (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    field k →ₐ[k] field k := by
  let I := algebraMap k (field k) i
  have hI : I^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k (field k)) hi
  have h2F : (2:field k)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (field k))).mpr h2
  exact CriticalEllipticEvaluation.embedding k (xMap I (x k)) (yMap I (x k) (y k))
    (CriticalDoubleCM.equation I _ _ hI h2F (x_nonzero k) (CriticalEllipticField.equation k))
    (map_transcendental I _ _ (isAlgebraic_algebraMap (x:=i)) hI h2F
      (x_nonzero k) (y_nonzero k) (CriticalEllipticField.equation k) (x_transcendental k))

@[simp] theorem map_x (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    map k i hi h2 (x k)=xMap (algebraMap k (field k) i) (x k) := by
  unfold map
  exact CriticalEllipticEvaluation.embedding_x k _ _ _ _

@[simp] theorem map_y (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    map k i hi h2 (y k)=yMap (algebraMap k (field k) i) (x k) (y k) := by
  unfold map
  exact CriticalEllipticEvaluation.embedding_y k _ _ _ _

/-- The CM field map adjoins an actual square root of its original x image. -/
theorem root_square (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0) :
    rootX (algebraMap k (field k) i) (x k) (y k)^2 = map k i hi h2 (x k) := by
  rw [map_x]
  apply CriticalDoubleCM.root_square
  · simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k (field k)) hi
  · simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k (field k))).mpr h2
  · exact x_nonzero k
  · exact CriticalEllipticField.equation k

end FourCorner.CriticalDoubleFieldMap
#print axioms FourCorner.CriticalDoubleFieldMap.map
#print axioms FourCorner.CriticalDoubleFieldMap.map_x
#print axioms FourCorner.CriticalDoubleFieldMap.map_y
#print axioms FourCorner.CriticalDoubleFieldMap.root_square
