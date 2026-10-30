import CriticalDirectQuartic

noncomputable section
namespace FourCorner.CriticalDirectMap
open CriticalConicParameter CriticalQuarticCubic CriticalDirectQuartic
variable {k : Type*} [Field k]
set_option autoImplicit false
set_option maxHeartbeats 1500000

def v (i a b : k) := parameter a b-i
def Y (i a b c : k) := ordinate i (parameter a b) c
def X (i a b c : k) := quarticX i (v i a b) (Y i a b c)
def x (i a b c : k) := (X i a b c-i)/scale i
def y (i a b c : k) := discriminantCoordinate (X i a b c) (v i a b)/(4*scale i)

def inverseX (i x : k) := i+scale i*x
def inverseL (i y : k) := 4*scale i*y
def inverseU (i x y : k) := inverseV (inverseX i x) (inverseL i y)+i
def inverseA (i x y : k) := first i (inverseU i x y)
def inverseB (i x y : k) := second i (inverseU i x y)
def inverseC (i x y : k) :=
  -quarticY i (inverseX i x) (inverseU i x y-i)/denominator i (inverseU i x y)

theorem inverseX_forward (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    inverseX i (x i a b c)=X i a b c := by
  dsimp [inverseX,x]
  field_simp [scale_nonzero i hi h2]
  ring

theorem inverseL_forward (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    inverseL i (y i a b c)=discriminantCoordinate (X i a b c) (v i a b) := by
  dsimp [inverseL,y]
  have h4 : (4:k) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  field_simp [scale_nonzero i hi h2,h4]

theorem quadratic_relation (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (ha : a ≠ 1) :
    quadratic i (X i a b c) (v i a b)=0 :=
  quadratic_of_quartic i _ _ hi (shifted_parameter_nonzero i a b hi h2 hb ha)
    (quartic_of_original i a b c hi h2 hb hc ha)

theorem elliptic_equation (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (ha : a ≠ 1) :
    y i a b c ^2=x i a b c ^3-x i a b c := by
  apply elliptic_of_scaled i _ _ hi h2
  change inverseL i (y i a b c)^2=cubic i (inverseX i (x i a b c))
  rw [inverseX_forward i a b c hi h2,inverseL_forward i a b c hi h2]
  exact cubic_of_quadratic i _ _ hi (quadratic_relation i a b c hi h2 hb hc ha)

/-- The ONLY additional inverse denominator is nonzero on the actual
b!=0 source open. No characteristic3 or other odd field is discarded. -/
theorem inverse_denominator (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (hshift : a^2-1 ≠ 0) :
    X i a b c ^2-1 ≠ 0 := by
  have ha : a ≠ 1 := by intro h; apply hshift; rw [h]; ring
  have hq := quadratic_relation i a b c hi h2 hb hc ha
  have h4 : (4:k) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  have h8 : (8:k) ≠ 0 := by convert pow_ne_zero 3 h2 using 1 <;> ring
  intro hz
  have he := sq_eq_sq_iff_eq_or_eq_neg.mp (show X i a b c^2=(1:k)^2 by rw [one_pow]; exact sub_eq_zero.mp hz)
  rcases he with he | he
  · have hii : 4*(i-1)=0 := by dsimp [quadratic] at hq; rw [he] at hq; linear_combination hq
    exact (mul_ne_zero h4 (sub_ne_zero.mpr (CriticalElliptic23.iota_ne_one i hi h2))) hii
  · have hv : v i a b+i=0 := by
      apply (mul_eq_zero.mp (show 8*(v i a b+i)=0 by
        dsimp [quadratic] at hq; rw [he] at hq; linear_combination hq)).resolve_left h8
    have hu : parameter a b=0 := by dsimp [v] at hv; linear_combination hv
    have hf := first_inverse i a b hi h2 hb ha
    rw [hu] at hf
    have hi0 := CriticalElliptic23.iota_nonzero i hi
    have ham : a = -1 := by
      dsimp [first,denominator] at hf
      simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,zero_sub,zero_add,div_neg,div_self hi0] using hf.symm
    apply hshift
    rw [ham]
    ring

theorem inverseU_forward (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (hshift : a^2-1 ≠ 0) :
    inverseU i (x i a b c) (y i a b c)=parameter a b := by
  dsimp only [inverseU]
  rw [inverseX_forward i a b c hi h2,inverseL_forward i a b c hi h2]
  rw [inverseV_discriminant _ _ h2 (inverse_denominator i a b c hi h2 hb hc hshift)]
  dsimp [v]
  ring

theorem inverseA_forward (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (hshift : a^2-1 ≠ 0) :
    inverseA i (x i a b c) (y i a b c)=a := by
  have ha : a ≠ 1 := by intro h; apply hshift; rw [h]; ring
  rw [inverseA,inverseU_forward i a b c hi h2 hb hc hshift]
  exact first_inverse i a b hi h2 hb ha

theorem inverseB_forward (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (hshift : a^2-1 ≠ 0) :
    inverseB i (x i a b c) (y i a b c)=b := by
  have ha : a ≠ 1 := by intro h; apply hshift; rw [h]; ring
  rw [inverseB,inverseU_forward i a b c hi h2 hb hc hshift]
  exact second_inverse i a b hi h2 hb ha

theorem inverseC_forward (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (hshift : a^2-1 ≠ 0) :
    inverseC i (x i a b c) (y i a b c)=c := by
  have ha : a ≠ 1 := by intro h; apply hshift; rw [h]; ring
  have hv := shifted_parameter_nonzero i a b hi h2 hb ha
  have hd := denominator_nonzero i a b hi h2 hb ha
  rw [inverseC,inverseX_forward i a b c hi h2,inverseU_forward i a b c hi h2 hb hc hshift]
  change -quarticY i (quarticX i (v i a b) (Y i a b c)) (v i a b)/denominator i (parameter a b)=c
  rw [quarticY_quarticX i (v i a b) (Y i a b c) hv]
  dsimp [Y,ordinate]
  field_simp [hd]

end FourCorner.CriticalDirectMap
#print axioms FourCorner.CriticalDirectMap.elliptic_equation
#print axioms FourCorner.CriticalDirectMap.inverse_denominator
#print axioms FourCorner.CriticalDirectMap.inverseA_forward
#print axioms FourCorner.CriticalDirectMap.inverseB_forward
#print axioms FourCorner.CriticalDirectMap.inverseC_forward
