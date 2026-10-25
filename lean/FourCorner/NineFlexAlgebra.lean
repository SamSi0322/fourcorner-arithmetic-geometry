import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs

namespace FourCorner

/-- Vieta's pair-product relation, proved directly for three distinct rational roots. -/
theorem cubic_no_linear_pair_relation {r s t m y : ℚ}
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : r ^ 3 + m * r ^ 2 - y = 0)
    (hs : s ^ 3 + m * s ^ 2 - y = 0)
    (ht : t ^ 3 + m * t ^ 2 - y = 0) : r*s + r*t + s*t = 0 := by
  have h1 : (r - s) * (r^2+r*s+s^2+m*(r+s)) = 0 := by
    linear_combination hr - hs
  have h2 : (r - t) * (r^2+r*t+t^2+m*(r+t)) = 0 := by
    linear_combination hr - ht
  have H1 := (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hrs)
  have H2 := (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hrt)
  have h3 : (s-t)*(r+s+t+m) = 0 := by linear_combination H1 - H2
  have H3 := (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hst)
  linear_combination -H1 + (r+s)*H3

/-- The rational flex parametrization after recovering the three actual tangent roots. -/
theorem flex_parameters_of_roots {A B r s t : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0)
    (hAr : A = r ^ 2 - s ^ 2) (hBr : B = r ^ 2 - t ^ 2)
    (hpair : r*s + r*t + s*t = 0) :
    ∃ k : ℚ, k ≠ 0 ∧ k ≠ 1 ∧ k ≠ -1 ∧ k ≠ -(1/2) ∧ k ≠ -2 ∧
      B/A = (1+2*k)/((1-k)*(1+k)^3) ∧
      ∃ r' : ℚ, r' ≠ 0 ∧ A = r'^2*(1-k^2) := by
  let k : ℚ := s/r
  have hk : k ≠ 0 := div_ne_zero hs hr
  have hkr : k*r=s := by dsimp [k]; field_simp
  have hk1 : k ≠ 1 := by
    intro he
    have : s=r := by rw [he] at hkr; linarith
    apply hA
    rw [hAr, this]
    ring
  have hkm1 : k ≠ -1 := by
    intro he
    have : s = -r := by rw [he] at hkr; linarith
    apply hA
    rw [hAr, this]
    ring
  have hkplus : 1+k ≠ 0 := by intro hz; apply hkm1; linarith
  have hkminus : 1-k ≠ 0 := by intro hz; apply hk1; linarith
  have htr : t = -r*k/(1+k) := by
    apply (eq_div_iff hkplus).2
    have hp : r * (t*(1+k)+r*k)=0 := by
      calc
        _ = r*s+r*t+s*t := by rw [←hkr]; ring
        _ = 0 := hpair
    have hp' := (mul_eq_zero.mp hp).resolve_left hr
    linarith
  have hAr' : A = r^2*(1-k^2) := by rw [hAr, ←hkr]; ring
  have hBr' : B = r^2*(1+2*k)/(1+k)^2 := by
    rw [hBr, htr]
    field_simp
    <;> ring
  have hkmhalf : k ≠ -(1/2) := by
    intro he
    apply hB
    rw [hBr', he]
    norm_num
  have hkm2 : k ≠ -2 := by
    intro he
    apply hAB
    rw [hAr', hBr', he]
    norm_num
    <;> ring
  refine ⟨k, hk, hk1, hkm1, hkmhalf, hkm2, ?_, r, hr, hAr'⟩
  have hkss : 1-k^2 ≠ 0 := by
    intro hz
    apply hA
    rw [hAr', hz]
    ring
  rw [hAr', hBr']
  field_simp [hkss]
  <;> ring

/-- The root recovered from the tangent at a cubic root e is an actual rational square root. -/
theorem flex_tangent_root {A B x y m e : ℚ}
    (hy : y ≠ 0) (hcurve : y^2=x*(x-A)*(x-B))
    (he : e*(e-A)*(e-B)=0)
    (hflex : ∀ z : ℚ, z*(z-A)*(z-B)-(m*(z-x)+y)^2=(z-x)^3) :
    x-e ≠ 0 ∧
    ((m*(e-x)+y)/(x-e))^2=x-e ∧
    ((m*(e-x)+y)/(x-e))^3 + m*((m*(e-x)+y)/(x-e))^2-y=0 := by
  have hx : x-e ≠ 0 := by
    intro hz
    have hxe : x=e := sub_eq_zero.mp hz
    rw [hxe, he] at hcurve
    exact hy (sq_eq_zero_iff.mp hcurve)
  have hf := hflex e
  rw [he] at hf
  have hsq : (m*(e-x)+y)^2=(x-e)^3 := by nlinarith [hf]
  have hroot : ((m*(e-x)+y)/(x-e))^2=x-e := by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hx)).2
    calc
      (m*(e-x)+y)^2 = (x-e)^3 := hsq
      _ = (x-e)*(x-e)^2 := by ring
  refine ⟨hx, hroot, ?_⟩
  have hc : ((m*(e-x)+y)/(x-e))^3 = m*(e-x)+y := by
    calc
      _ = ((m*(e-x)+y)/(x-e)) * (((m*(e-x)+y)/(x-e))^2) := by ring
      _ = ((m*(e-x)+y)/(x-e))*(x-e) := by rw [hroot]
      _ = m*(e-x)+y := div_mul_cancel₀ _ hx
  rw [hc, hroot]
  ring

/-- The complete flex parametrization from the triple-intersection identity. -/
theorem flex_parameters_of_tangent {A B x y m : ℚ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ≠ B)
    (hy : y ≠ 0) (hcurve : y^2=x*(x-A)*(x-B))
    (hflex : ∀ z : ℚ, z*(z-A)*(z-B)-(m*(z-x)+y)^2=(z-x)^3) :
    ∃ k : ℚ, k ≠ 0 ∧ k ≠ 1 ∧ k ≠ -1 ∧ k ≠ -(1/2) ∧ k ≠ -2 ∧
      B/A = (1+2*k)/((1-k)*(1+k)^3) ∧
      ∃ r : ℚ, r ≠ 0 ∧ A = r^2*(1-k^2) := by
  let r := (m*(0-x)+y)/(x-0)
  let s := (m*(A-x)+y)/(x-A)
  let t := (m*(B-x)+y)/(x-B)
  obtain ⟨hx0,hr2,hr3⟩ := flex_tangent_root hy hcurve (e:=0) (by ring) hflex
  obtain ⟨hxA,hs2,hs3⟩ := flex_tangent_root hy hcurve (e:=A) (by ring) hflex
  obtain ⟨hxB,ht2,ht3⟩ := flex_tangent_root hy hcurve (e:=B) (by ring) hflex
  have hr : r ≠ 0 := by intro h; change r^2=x-0 at hr2; rw [h] at hr2; exact hx0 (by linarith)
  have hs : s ≠ 0 := by intro h; change s^2=x-A at hs2; rw [h] at hs2; exact hxA (by linarith)
  have ht : t ≠ 0 := by intro h; change t^2=x-B at ht2; rw [h] at ht2; exact hxB (by linarith)
  have hrs : r ≠ s := by
    intro h
    change r^2=x-0 at hr2
    change s^2=x-A at hs2
    rw [h] at hr2
    exact hA (by linarith)
  have hrt : r ≠ t := by
    intro h
    change r^2=x-0 at hr2
    change t^2=x-B at ht2
    rw [h] at hr2
    exact hB (by linarith)
  have hst : s ≠ t := by
    intro h
    change s^2=x-A at hs2
    change t^2=x-B at ht2
    rw [h] at hs2
    exact hAB (by linarith)
  have hp : r*s+r*t+s*t=0 := cubic_no_linear_pair_relation hrs hrt hst hr3 hs3 ht3
  apply flex_parameters_of_roots hA hB hAB hr hs ht _ _ hp
  · change A = r^2-s^2
    change r^2=x-0 at hr2
    change s^2=x-A at hs2
    linarith
  · change B = r^2-t^2
    change r^2=x-0 at hr2
    change t^2=x-B at ht2
    linarith

#print axioms cubic_no_linear_pair_relation
#print axioms flex_parameters_of_roots
#print axioms flex_tangent_root
#print axioms flex_parameters_of_tangent
end FourCorner
