import HasseProjectivePoint

/-! Rational anchor gauge and nonzero literal tangent coefficient for §05.
These theorems build arithmetic inputs from a genuine rational source point.
They do not assert a local invariant, a Brauer-class extension or reciprocity.
-/
namespace FourCorner.HasseAnchorChoice

open CompleteSource11 HasseRationalSource HasseProjectivePoint

def anchorZ (p z w : ℚ) : ℚ := (p-1)*w-2*(p+1)*z
def anchorU (p z w t : ℚ) : ℚ := p*(p+1)*(w+2*t+2*z)
def anchorT (p z w t : ℚ) : ℚ := -(p+1)*((p-1)*w+2*p*t+2*(p-1)*z)
def separation (p z w t : ℚ) : ℚ := anchorZ p z w*t-z*anchorT p z w t
def secondPolar (p Z U T z w t : ℚ) : ℚ :=
  (p-1)*anchorU p z w t*U-p*anchorT p z w t*T+p*(p+1)*anchorZ p z w*Z

/-- Invertibility of the exact manuscript anchor transformation, with its
nonvanishing derived from the original tuple rather than postulated. -/
theorem anchor_transform_nonzero (p z w t : ℚ) (hp : p ≠ 0) (hb : p+1 ≠ 0)
    (h0 : ¬ (z=0 ∧ t=0 ∧ w=0)) :
    ¬ (anchorZ p z w=0 ∧ anchorU p z w t=0 ∧ anchorT p z w t=0) := by
  rintro ⟨hz,hu,ht⟩
  have hu' : w+2*t+2*z=0 := by
    exact (mul_eq_zero.mp hu).resolve_left (mul_ne_zero hp hb)
  have ht' : (p-1)*w+2*p*t+2*(p-1)*z=0 := by
    exact (mul_eq_zero.mp ht).resolve_left (neg_ne_zero.mpr hb)
  have hzt : 2*z+t=0 := by
    apply (mul_eq_zero.mp (show p*(2*z+t)=0 by
      dsimp [anchorZ] at hz
      linear_combination (1/2 : ℚ)*ht' - (1/2 : ℚ)*hz)).resolve_left hp
  have hwz : w=2*z := by linear_combination hu' - 2*hzt
  have hz0 : z=0 := by
    dsimp [anchorZ] at hz
    rw [hwz] at hz
    nlinarith
  exact h0 ⟨hz0,by linarith,by linarith⟩

/-- The exact two sign separations cannot both vanish at a rational DU point. -/
theorem exists_separated_sign (p z v w t : ℚ) (hp : 1<p) (hz : z ≠ 0)
    (h : OmitU p z v w t) :
    ∃ w' : ℚ, (w'=w ∨ w'=-w) ∧ OmitU p z v w' t ∧ separation p z w' t ≠ 0 := by
  have htz : t+z ≠ 0 := by
    intro htz
    have ht : t= -z := by linarith
    have hh := h.2
    rw [ht] at hh
    have hl : 0 ≤ (p-1)*w^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hr : 0 < (p+1)*z^2 := mul_pos (by linarith) (sq_pos_of_ne_zero hz)
    nlinarith
  by_cases hs : separation p z w t ≠ 0
  · exact ⟨w,Or.inl rfl,h,hs⟩
  · refine ⟨-w,Or.inr rfl,?_,?_⟩
    · simpa only [OmitU,neg_sq] using h
    · intro hm
      have hs0 : separation p z w t=0 := not_ne_iff.mp hs
      have hsum : separation p z w t+separation p z (-w) t =
          4*(p-1)*(p+1)*z*(t+z) := by
        dsimp [separation,anchorZ,anchorT]
        ring
      have hprod : 4*(p-1)*(p+1)*z*(t+z) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
          (by linarith)) (by linarith)) hz) htz
      exact hprod (by rw [hs0,hm,zero_add] at hsum; exact hsum.symm)

/-- Polar nonvanishing follows from the two actual conic equations and a
positive sum of squares. No assertion about Brauer evaluation is used. -/
theorem conic_polar_ne_zero (p Z U T z u t : ℚ) (hp : 1<p)
    (hP : (p-1)*U^2-p*T^2+p*(p+1)*Z^2=0)
    (hQ : (p-1)*u^2-p*t^2+p*(p+1)*z^2=0)
    (hsep : z*T-Z*t ≠ 0) : (p-1)*u*U-p*t*T+p*(p+1)*z*Z ≠ 0 := by
  intro hL
  have he : (p-1)*(t*U-T*u)^2+p*(p+1)*(t*Z-T*z)^2=0 := by
    linear_combination t^2*hP + T^2*hQ - 2*T*t*hL
  have hpos : 0 < p*(p+1)*(t*Z-T*z)^2 := by
    apply mul_pos (mul_pos (by linarith) (by linarith))
    apply sq_pos_of_ne_zero
    intro hh
    apply hsep
    linear_combination -hh
  have hnon : 0 ≤ (p-1)*(t*U-T*u)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  linarith

/-- Exact arithmetic anchor construction and a nonzero rational second polar,
from every full source point. The only sign choice is W ↦ ±W. -/
theorem source_anchor_coefficient (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) :
    ∃ w : ℚ, (w=P.W ∨ w= -P.W) ∧ OmitU p P.Z P.V w P.T ∧
      separation p P.Z w P.T ≠ 0 ∧
      (p-1)*(anchorU p P.Z w P.T)^2-p*(anchorT p P.Z w P.T)^2+
        p*(p+1)*(anchorZ p P.Z w)^2=0 ∧
      -p*secondPolar p P.Z P.U P.T P.Z w P.T ≠ 0 := by
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨hz,hu,hv,hw,ht⟩ := coordinates_ne_zero p hp P
  have hDU := (omission_equations p P.Z P.U P.V P.W P.T hp0 P.equations).1
  obtain ⟨w,hs,hDU',hsep⟩ := exists_separated_sign p P.Z P.V P.W P.T hp hz hDU
  have hanc := anchor_conic p P.Z P.V w P.T hDU'
  change (p-1)*(anchorU p P.Z w P.T)^2-p*(anchorT p P.Z w P.T)^2+
    p*(p+1)*(anchorZ p P.Z w)^2=0 at hanc
  have hpol : secondPolar p P.Z P.U P.T P.Z w P.T ≠ 0 := by
    apply conic_polar_ne_zero p P.Z P.U P.T (anchorZ p P.Z w)
      (anchorU p P.Z w P.T) (anchorT p P.Z w P.T) hp
    · linear_combination -P.equations.2.2
    · exact hanc
    · exact hsep
  exact ⟨w,hs,hDU',hsep,hanc,mul_ne_zero (neg_ne_zero.mpr hp0) hpol⟩

/-- Positive-definite arithmetic fixes the real gauge of the exact anchor.
This is the elementary source-anchor argument from high11, now attached to
the accepted homogeneous-point interface. -/
theorem opposite_anchor_time (p z v w t : ℚ) (hp : 1<p) (hz : z ≠ 0)
    (h : OmitU p z v w t) : anchorT p z w t*t < 0 := by
  have ha : 0<p-1 := by linarith
  have hb : 0<p+1 := by linarith
  have hp' : 0<p := by linarith
  have hz2 := sq_pos_of_ne_zero hz
  have ht2 : 0<t^2 := by nlinarith [h.1,sq_nonneg v]
  have hsq : 0<(2*p*t+2*(p-1)*z)^2-((p-1)*w)^2 := by
    have hid : (2*p*t+2*(p-1)*z)^2-((p-1)*w)^2 =
        2*((p*t+2*(p-1)*z)^2+t^2+4*(p-1)*z^2) := by
      linear_combination -(p-1)*h.2
    rw [hid]
    positivity
  have hst : 0<(2*p*t+2*(p-1)*z)*t := by
    have hc : 0≤(p-1)*(t+z)^2 := mul_nonneg ha.le (sq_nonneg _)
    have hv : 0≤(p+1)*v^2 := mul_nonneg hb.le (sq_nonneg _)
    have hpos : 0<(4*p*(p+1)-(p-1))*z^2 := by
      have : 0<4*p*(p+1)-(p-1) := by nlinarith
      exact mul_pos this hz2
    nlinarith [h.1]
  have hscaled := mul_pos hsq ht2
  have hsum : 0<((p-1)*w+2*p*t+2*(p-1)*z)*t := by
    nlinarith [sq_nonneg (((p-1)*w)*t)]
  dsimp [anchorT]
  nlinarith [mul_pos hb hsum]

theorem conic_polar_positive (p Z U T z u t : ℚ) (hp : 1<p)
    (hP : (p-1)*U^2-p*T^2+p*(p+1)*Z^2=0)
    (hQ : (p-1)*u^2-p*t^2+p*(p+1)*z^2=0)
    (hsep : z*T-Z*t ≠ 0) (ht : t*T<0) :
    0<(p-1)*u*U-p*t*T+p*(p+1)*z*Z := by
  have he : (p-1)*(t*U-T*u)^2+p*(p+1)*(t*Z-T*z)^2 =
      -2*t*T*((p-1)*u*U-p*t*T+p*(p+1)*z*Z) := by
    linear_combination t^2*hP+T^2*hQ
  have hpos : 0<p*(p+1)*(t*Z-T*z)^2 := by
    apply mul_pos (mul_pos (by linarith) (by linarith))
    apply sq_pos_of_ne_zero
    intro hh
    apply hsep
    linear_combination -hh
  have hnon : 0≤(p-1)*(t*U-T*u)^2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hsum : 0<(p-1)*(t*U-T*u)^2+p*(p+1)*(t*Z-T*z)^2 := by linarith
  rw [he] at hsum
  exact (mul_pos_iff_of_pos_left (show 0< -2*t*T by nlinarith)).mp hsum

/-- All input for the literal rational tangent symbol is constructed from
the original source point, including the strict negative real coefficient. -/
structure TangentData (p : ℚ) (P : HomogeneousPoint p) where
  w : ℚ
  sign : w=P.W ∨ w= -P.W
  omission : OmitU p P.Z P.V w P.T
  separated : separation p P.Z w P.T ≠ 0
  coefficient_negative : -p*secondPolar p P.Z P.U P.T P.Z w P.T<0

noncomputable def tangentData (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) :
    TangentData p P := by
  apply Classical.choice
  obtain ⟨w,hs,hDU,hsep,hanc,_⟩ := source_anchor_coefficient p hp P
  have hz := (coordinates_ne_zero p hp P).1
  have htime := opposite_anchor_time p P.Z P.V w P.T hp hz hDU
  have hpos : 0<secondPolar p P.Z P.U P.T P.Z w P.T := by
    apply conic_polar_positive p P.Z P.U P.T (anchorZ p P.Z w)
      (anchorU p P.Z w P.T) (anchorT p P.Z w P.T) hp
    · linear_combination -P.equations.2.2
    · exact hanc
    · exact hsep
    · exact htime
  exact ⟨⟨w,hs,hDU,hsep,mul_neg_of_neg_of_pos (by linarith) hpos⟩⟩

#print axioms anchor_transform_nonzero
#print axioms exists_separated_sign
#print axioms conic_polar_ne_zero
#print axioms source_anchor_coefficient
#print axioms opposite_anchor_time
#print axioms conic_polar_positive
#print axioms tangentData

end FourCorner.HasseAnchorChoice
