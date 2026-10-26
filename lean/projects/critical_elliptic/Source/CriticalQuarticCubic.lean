import CriticalConicParameter

noncomputable section
namespace FourCorner.CriticalQuarticCubic
variable {k : Type*} [Field k]
set_option autoImplicit false
set_option maxHeartbeats 1500000

def quartic (i v : k) : k :=
  v^4-4*v^3+(6-6*i)*v^2+(4+4*i)*v+2*i
def quadratic (i X v : k) : k :=
  (X^2-1)*v^2+4*(1-X)*v-2+6*i-2*(1+i)*X
def cubic (i X : k) : k := 8*(1+i)*((X-i)^3+2*i*(X-i))
def discriminantCoordinate (X v : k) : k := 2*(X^2-1)*v+4*(1-X)
def quarticX (i v Y : k) : k := (Y+(1+i)+2*v)/v^2
def quarticY (i X v : k) : k := X*v^2-(1+i)-2*v
def inverseV (X L : k) : k := (L-4*(1-X))/(2*(X^2-1))
def scale (i : k) : k := 1-i

theorem cleared_identity (i X v : k) (hi : i^2 = -1) :
    quarticY i X v ^2-quartic i v = v^2*quadratic i X v := by
  dsimp [quarticY,quartic,quadratic]
  linear_combination hi

theorem quarticY_quarticX (i v Y : k) (hv : v ≠ 0) :
    quarticY i (quarticX i v Y) v = Y := by
  dsimp [quarticY,quarticX]
  field_simp [hv]
  ring

theorem quarticX_quarticY (i X v : k) (hv : v ≠ 0) :
    quarticX i v (quarticY i X v) = X := by
  dsimp [quarticY,quarticX]
  field_simp [hv]
  ring

theorem quadratic_of_quartic (i v Y : k) (hi : i^2 = -1) (hv : v ≠ 0)
    (hY : Y^2=quartic i v) : quadratic i (quarticX i v Y) v=0 := by
  have h := cleared_identity i (quarticX i v Y) v hi
  rw [quarticY_quarticX i v Y hv,hY,sub_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hv)

theorem discriminant_identity (i X v : k) (hi : i^2 = -1) :
    discriminantCoordinate X v ^2-cubic i X = 4*(X^2-1)*quadratic i X v := by
  dsimp [discriminantCoordinate,cubic,quadratic]
  linear_combination (24*X^2-40*X+8*i^2+i*(24-24*X)+8)*hi

theorem cubic_of_quadratic (i X v : k) (hi : i^2 = -1)
    (hQ : quadratic i X v=0) : discriminantCoordinate X v ^2=cubic i X := by
  have h := discriminant_identity i X v hi
  rw [hQ,mul_zero] at h
  exact sub_eq_zero.mp h

theorem inverseV_discriminant (X v : k) (h2 : (2:k) ≠ 0) (hX : X^2-1 ≠ 0) :
    inverseV X (discriminantCoordinate X v) = v := by
  dsimp [inverseV,discriminantCoordinate]
  field_simp [h2,hX]
  ring

theorem discriminant_inverseV (X L : k) (h2 : (2:k) ≠ 0) (hX : X^2-1 ≠ 0) :
    discriminantCoordinate X (inverseV X L) = L := by
  dsimp [inverseV,discriminantCoordinate]
  field_simp [h2,hX]
  ring

theorem quadratic_of_cubic (i X L : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hX : X^2-1 ≠ 0) (hL : L^2=cubic i X) : quadratic i X (inverseV X L)=0 := by
  have h := discriminant_identity i X (inverseV X L) hi
  rw [discriminant_inverseV X L h2 hX,hL,sub_self] at h
  have h4 : (4:k) ≠ 0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero h4 hX)

theorem quartic_of_quadratic (i X v : k) (hi : i^2 = -1) (hQ : quadratic i X v=0) :
    quarticY i X v ^2=quartic i v := by
  have h := cleared_identity i X v hi
  rw [hQ,mul_zero] at h
  exact sub_eq_zero.mp h

/-- This scaling gives the actual y²=x³−x cubic over ANY field with i²=−1,
without a square-root extension, characteristic-zero or perfectness premise. -/
theorem scaling_identity (i x y : k) (hi : i^2 = -1) :
    (4*scale i*y)^2-cubic i (i+scale i*x) =
      16*scale i^2*(y^2-(x^3-x)) := by
  dsimp [scale,cubic]
  linear_combination (8*x*(i-1)*(i*x^2-x^2+2))*hi

theorem scale_nonzero (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) : scale i ≠ 0 :=
  sub_ne_zero.mpr (CriticalElliptic23.iota_ne_one i hi h2).symm

theorem elliptic_of_scaled (i x y : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (h : (4*scale i*y)^2=cubic i (i+scale i*x)) : y^2=x^3-x := by
  have hs := scaling_identity i x y hi
  rw [h,sub_self] at hs
  have h16 : (16:k) ≠ 0 := by convert pow_ne_zero 4 h2 using 1 <;> ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hs.symm).resolve_left
    (mul_ne_zero h16 (pow_ne_zero _ (scale_nonzero i hi h2))))

end FourCorner.CriticalQuarticCubic
#print axioms FourCorner.CriticalQuarticCubic.quadratic_of_quartic
#print axioms FourCorner.CriticalQuarticCubic.quadratic_of_cubic
#print axioms FourCorner.CriticalQuarticCubic.elliptic_of_scaled
#print axioms FourCorner.CriticalQuarticCubic.inverseV_discriminant
