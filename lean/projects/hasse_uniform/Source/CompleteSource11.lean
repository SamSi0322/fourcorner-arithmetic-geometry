import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
namespace FourCorner.CompleteSource11
variable {K : Type*} [Field K] [CharZero K]
def Source (p Z U V W T : K) : Prop :=
  p*V^2 = 2*(p-1)*(U^2-p*Z^2) ∧
  p*W^2 = 2*(p+1)*(U^2+p*Z^2) ∧
  p*T^2 = (p-1)*U^2+p*(p+1)*Z^2
def OmitU (p z v w t : K) : Prop :=
  v^2 = 2*t^2-4*p*z^2 ∧ (p-1)*w^2 = 2*(p+1)*(t^2-2*z^2)
def OmitW (p Z U V T : K) : Prop :=
  V^2 = 2*T^2-4*p*Z^2 ∧ (p-1)*U^2 = p*T^2-p*(p+1)*Z^2

theorem omission_equations (p Z U V W T : K) (hp : p ≠ 0)
    (h : Source p Z U V W T) : OmitU p Z V W T ∧ OmitW p Z U V T := by
  rcases h with ⟨hV,hW,hT⟩
  have hfirst : V^2 = 2*T^2-4*p*Z^2 := by
    apply (mul_left_cancel₀ hp)
    linear_combination hV - 2*hT
  refine ⟨⟨hfirst, ?_⟩, ⟨hfirst, ?_⟩⟩
  · apply (mul_left_cancel₀ hp)
    linear_combination (p-1)*hW - 2*(p+1)*hT
  · linear_combination -hT

theorem omission_U_no_basepoint (p Z U V W T : K) (ha : p-1 ≠ 0)
    (h : Source p Z U V W T) (hZ : Z=0) (hV : V=0) (hW : W=0)
    (hT : T=0) : U=0 := by
  have hh := h.2.2
  rw [hZ,hT] at hh
  have hu : (p-1)*U^2=0 := by linear_combination -hh
  exact (sq_eq_zero_iff).mp (mul_eq_zero.mp hu |>.resolve_left ha)

theorem omission_W_no_basepoint (p Z U V W T : K) (hp : p ≠ 0)
    (h : Source p Z U V W T) (hZ : Z=0) (hU : U=0) (hV : V=0)
    (hT : T=0) : W=0 := by
  have hh := h.2.1
  rw [hZ,hU] at hh
  have hw : p*W^2=0 := by linear_combination hh
  exact (sq_eq_zero_iff).mp (mul_eq_zero.mp hw |>.resolve_left hp)

theorem four_ordered_squares (p Z U V W T : K) (hp : p ≠ 0) (hZ : Z ≠ 0)
    (h : Source p Z U V W T) :
    (U/Z)^2 = p*(U^2/(p*Z^2)) ∧
    (V/Z)^2 = 2*(p-1)*(U^2/(p*Z^2)-1) ∧
    (W/Z)^2 = 2*(p+1)*(U^2/(p*Z^2)+1) ∧
    (T/Z)^2 = (p-1)*(U^2/(p*Z^2))+p+1 := by
  rcases h with ⟨hV,hW,hT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp; <;> ring
  · field_simp; linear_combination hV
  · field_simp; linear_combination hW
  · field_simp; linear_combination hT

theorem anchor_conic (p z v w t : K) (h : OmitU p z v w t) :
    (p-1)*(p*(p+1)*(w+2*t+2*z))^2 -
      p*(-(p+1)*((p-1)*w+2*p*t+2*(p-1)*z))^2 +
      p*(p+1)*((p-1)*w-2*(p+1)*z)^2 = 0 := by
  linear_combination 2*p^2*(p+1)*h.2
def Partner (p A B C ζ : K) : Prop :=
  (-(p-1))*A^2-(-(p-1))*B^2 = (8*p/(p-1)^2)*ζ^2 ∧
  (-(p-1))*A^2-C^2 = (-8*p*(p+1)/(p-1)^3)*ζ^2

/-- A genuine nonzero point at infinity whenever c is square. -/
theorem partner_infinity (p r : K) (hr : r^2 = -(p-1)) :
    Partner p 1 1 r 0 := by
  constructor <;> simp [hr] <;> ring

/-- The second explicit partner point, with its actual ordered coordinates. -/
theorem partner_root_R (p r : K) (hp : p ≠ 0) (ha : p-1 ≠ 0)
    (hr : r^2 = (p+1)/(2*p)) :
    Partner p ((4*p/(p-1)^2)*r) (4*p/(p-1)^2) 0 1 := by
  constructor
  · rw [mul_pow, hr]
    field_simp
    <;> ring
  · rw [mul_pow, hr]
    field_simp
    <;> ring

theorem first_polar_identity (p z v t Z V T : K)
    (ha : v^2 = 2*t^2-4*p*z^2) (hP : V^2 = 2*T^2-4*p*Z^2) :
    (z*V-v*Z)^2-2*(z*T-t*Z)^2 =
      -2*z*Z*(v*V-2*t*T+4*p*z*Z) := by
  linear_combination z^2*hP + Z^2*ha

theorem second_polar_identity (p z u t Z U T : K)
    (ha : (p-1)*u^2-p*t^2+p*(p+1)*z^2 = 0)
    (hP : (p-1)*U^2-p*T^2+p*(p+1)*Z^2 = 0) :
    (p-1)*(z*U-u*Z)^2-p*(z*T-t*Z)^2 =
      -2*z*Z*((p-1)*u*U-p*t*T+p*(p+1)*z*Z) := by
  linear_combination z^2*hP + Z^2*ha

#print axioms first_polar_identity
#print axioms second_polar_identity
#print axioms partner_infinity
#print axioms partner_root_R
#print axioms omission_equations
#print axioms omission_U_no_basepoint
#print axioms omission_W_no_basepoint
#print axioms four_ordered_squares
#print axioms anchor_conic
end FourCorner.CompleteSource11
