import CriticalQuarticCubic

noncomputable section
namespace FourCorner.CriticalDirectQuartic
open CriticalConicParameter CriticalQuarticCubic
variable {k : Type*} [Field k]
set_option autoImplicit false
set_option maxHeartbeats 1500000

def numerator (i u : k) : k := u^2-2*u+i
def ordinate (i u c : k) : k := -c*denominator i u

theorem quartic_identity (i u : k) (hi : i^2 = -1) :
    denominator i u ^2+(1+i)*(numerator i u ^2-denominator i u ^2)=quartic i (u-i) := by
  dsimp [denominator,numerator,quartic]
  linear_combination (-i^2+i*(4*u+2)-2*u^2-4*u)*hi

theorem quartic_of_conic_coordinates (i u c : k) (hi : i^2 = -1)
    (hd : denominator i u ≠ 0)
    (hc : c^2-1=(1+i)*(first i u ^2-1)) :
    ordinate i u c ^2=quartic i (u-i) := by
  rw [←quartic_identity i u hi]
  dsimp only [ordinate,numerator]
  dsimp only [first] at hc
  field_simp [hd] at hc
  linear_combination hc

theorem original_of_quartic (i u Y : k) (hi : i^2 = -1)
    (hd : denominator i u ≠ 0) (hY : Y^2=quartic i (u-i)) :
    second i u ^2-1=i*(first i u ^2-1) ∧
    (-Y/denominator i u)^2-1=(1+i)*(first i u ^2-1) := by
  refine ⟨conic_equation i u hi hd,?_⟩
  rw [←quartic_identity i u hi] at hY
  dsimp only [first]
  field_simp [hd]
  dsimp only [numerator] at hY
  linear_combination hY

theorem quartic_of_original (i a b c : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1)) (ha : a ≠ 1) :
    ordinate i (parameter a b) c ^2=quartic i (parameter a b-i) := by
  apply quartic_of_conic_coordinates i _ c hi (denominator_nonzero i a b hi h2 hb ha)
  rw [first_inverse i a b hi h2 hb ha]
  exact hc

theorem parameter_recovery (i u : k) (h2 : (2:k) ≠ 0) (hd : denominator i u ≠ 0)
    (hu : u-i ≠ 0) : parameter (first i u) (second i u)=u := by
  have hdiff : i-u ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hu).symm
  have hnum : 2*(i-u) ≠ 0 := mul_ne_zero h2 hdiff
  have he : first i u-1 = 2*(i-u)/denominator i u := by
    dsimp [first]
    field_simp [hd]
    dsimp [denominator]
    ring
  have hf : second i u-1 = 2*u*(i-u)/denominator i u := by
    dsimp [second]
    field_simp [hd]
    dsimp [denominator]
    ring
  dsimp only [parameter]
  rw [he,hf]
  field_simp [hd,h2,hdiff]

end FourCorner.CriticalDirectQuartic
#print axioms FourCorner.CriticalDirectQuartic.quartic_of_original
#print axioms FourCorner.CriticalDirectQuartic.original_of_quartic
#print axioms FourCorner.CriticalDirectQuartic.parameter_recovery
