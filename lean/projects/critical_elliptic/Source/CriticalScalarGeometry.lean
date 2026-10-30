import CriticalProjCoordinates23
import CriticalAmbientChart

noncomputable section
namespace FourCorner.CriticalScalarGeometry
open CriticalElliptic23 CriticalAmbientChart
variable {k : Type*} [Field k]

theorem zero_unique (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (v : Fin 4 → k) (hc : CriticalCoordinates i v) (hn : ∃ j,v j≠0)
    (a b : Fin 4) (ha : v a=0) (hb : v b=0) : a=b := by
  have hi0 := iota_nonzero i hi
  have him := iota_ne_one i hi h2
  have hip := iota_add_one_nonzero i hi h2
  by_cases hv0 : v 0=0
  · have hv1 : v 1≠0 := by
      intro h
      have he := hc.1
      have hf := hc.2
      simp only [Shift,hv0,h,zero_pow (by decide : 2≠0),sub_zero,mul_zero] at he hf
      obtain ⟨j,hj⟩:=hn
      fin_cases j <;> simp_all
    have hv2 : v 2≠0 := by
      intro h
      have he := hc.1
      simp only [Shift,hv0,h,zero_pow (by decide : 2≠0),sub_zero] at he
      exact (mul_ne_zero hi0 (pow_ne_zero 2 hv1)) he.symm
    have hv3 : v 3≠0 := by
      intro h
      have he := hc.2
      simp only [Shift,hv0,h,zero_pow (by decide : 2≠0),sub_zero] at he
      exact (mul_ne_zero hip (pow_ne_zero 2 hv1)) he.symm
    fin_cases a <;> fin_cases b <;> simp_all
  by_cases hv1 : v 1=0
  · have hv2 : v 2≠0 := by
      intro h
      have he := hc.1
      simp only [Shift,hv1,h,zero_pow (by decide : 2≠0),zero_sub] at he
      have hz : (i-1)*v 0^2=0 := by linear_combination he
      exact (mul_ne_zero (sub_ne_zero.mpr him) (pow_ne_zero 2 hv0)) hz
    have hv3 : v 3≠0 := by
      intro h
      have he := hc.2
      simp only [Shift,hv1,h,zero_pow (by decide : 2≠0),zero_sub] at he
      have hz : i*v 0^2=0 := by linear_combination he
      exact (mul_ne_zero hi0 (pow_ne_zero 2 hv0)) hz
    fin_cases a <;> fin_cases b <;> simp_all
  by_cases hv2 : v 2=0
  · have hv3 : v 3≠0 := fun h => not_both_last_zero i v hc hn hv2 h
    fin_cases a <;> fin_cases b <;> simp_all
  · fin_cases a <;> fin_cases b <;> simp_all

def coefficient0 (i : k) : Fin 4 → k := ![i-1,-i,1,0]
def coefficient1 (i : k) : Fin 4 → k := ![i,-(1+i),0,1]
def minor (i : k) (a b : Fin 4) : k :=
  coefficient0 i a*coefficient1 i b-coefficient0 i b*coefficient1 i a

theorem minor_nonzero (i : k) (hi : i^2= -1) (h2 : (2:k)≠0)
    (a b : Fin 4) (hab : a≠b) : minor i a b≠0 := by
  have hi0 := iota_nonzero i hi
  have him := iota_ne_one i hi h2
  have hip := iota_add_one_nonzero i hi h2
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | skip
  all_goals dsimp [minor,coefficient0,coefficient1]
  all_goals intro hz
  all_goals first
    | exact one_ne_zero (by first | linear_combination hz | linear_combination -hz)
    | exact hi0 (by first | linear_combination hz | linear_combination -hz)
    | exact him (by first | linear_combination hz | linear_combination -hz)
    | exact hip (by first | linear_combination hz | linear_combination -hz)

end FourCorner.CriticalScalarGeometry
#print axioms FourCorner.CriticalScalarGeometry.zero_unique
#print axioms FourCorner.CriticalScalarGeometry.minor_nonzero
