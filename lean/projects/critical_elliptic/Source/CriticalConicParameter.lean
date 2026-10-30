import CriticalElliptic23

noncomputable section
namespace FourCorner.CriticalConicParameter
variable {k : Type*} [Field k]
set_option autoImplicit false

/-- Projection of the actual (V0,V1,V2) conic from (1,1,1).
This is a birational CONIC parameter, not the degree4 elliptic quotient. -/
def parameter (a b : k) : k := (b-1)/(a-1)
def denominator (i u : k) : k := u^2-i
def first (i u : k) : k := (u^2-2*u+i)/(denominator i u)
def second (i u : k) : k := (-u^2+2*i*u-i)/(denominator i u)

theorem conic_line (i a b : k) (h : b^2-1=i*(a^2-1)) (ha : a ≠ 1) :
    denominator i (parameter a b)*(a-1) = 2*(i-parameter a b) := by
  dsimp [denominator,parameter]
  field_simp [sub_ne_zero.mpr ha]
  linear_combination h

theorem denominator_nonzero (i a b : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (h : b^2-1=i*(a^2-1)) (ha : a ≠ 1) : denominator i (parameter a b) ≠ 0 := by
  have hl := conic_line i a b h ha
  intro hz
  rw [hz,zero_mul] at hl
  have hu : parameter a b = i := by
    have hh := (mul_eq_zero.mp hl.symm).resolve_left h2
    exact (sub_eq_zero.mp hh).symm
  have hip := CriticalElliptic23.iota_add_one_nonzero i hi h2
  apply hip
  dsimp [denominator] at hz
  rw [hu,hi] at hz
  linear_combination -hz

theorem shifted_parameter_nonzero (i a b : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (h : b^2-1=i*(a^2-1)) (ha : a ≠ 1) : parameter a b-i ≠ 0 := by
  have hl := conic_line i a b h ha
  have hd := denominator_nonzero i a b hi h2 h ha
  intro hz
  apply (mul_ne_zero hd (sub_ne_zero.mpr ha))
  rw [hl,sub_eq_zero.mp hz,sub_self,mul_zero]

theorem first_inverse (i a b : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (h : b^2-1=i*(a^2-1)) (ha : a ≠ 1) : first i (parameter a b) = a := by
  have hl := conic_line i a b h ha
  have hd := denominator_nonzero i a b hi h2 h ha
  apply (div_eq_iff hd).mpr
  dsimp [denominator] at hl
  dsimp only [denominator]
  linear_combination -hl

theorem second_inverse (i a b : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (h : b^2-1=i*(a^2-1)) (ha : a ≠ 1) : second i (parameter a b) = b := by
  have hd := denominator_nonzero i a b hi h2 h ha
  have hf := first_inverse i a b hi h2 h ha
  have hb : b = 1+parameter a b*(a-1) := by
    dsimp [parameter]
    field_simp [sub_ne_zero.mpr ha]
    ring
  calc
    second i (parameter a b) = 1+parameter a b*(first i (parameter a b)-1) := by
      dsimp [first,second]
      field_simp [hd]
      dsimp [denominator]
      ring
    _ = b := by rw [hf,←hb]

theorem conic_equation (i u : k) (hi : i^2 = -1) (hd : denominator i u ≠ 0) :
    second i u ^2-1=i*(first i u ^2-1) := by
  dsimp [first,second]
  field_simp [hd]
  dsimp [denominator]
  ring

end FourCorner.CriticalConicParameter
#print axioms FourCorner.CriticalConicParameter.first_inverse
#print axioms FourCorner.CriticalConicParameter.second_inverse
#print axioms FourCorner.CriticalConicParameter.conic_equation
