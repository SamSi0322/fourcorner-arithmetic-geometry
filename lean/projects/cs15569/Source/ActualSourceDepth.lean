import ActualTorsionOrders

noncomputable section
namespace FourCorner.CommonSource

/-- The nonzero factors of an ordered affine source exclude every two-torsion
point, including infinity. -/
theorem finite_source_not_two_torsion {n a b : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (ha : a ≠ 0) (ham : a-n ≠ 0) (hap : a+n ≠ 0) :
    2 • finitePoint hn hQ ≠ 0 := by
  intro ht
  rcases (two_torsion_iff hn _).mp ht with h | h | h | h
  · have hh := congrArg coordinates h
    simp [coordinates,O,finitePoint] at hh
  · have hh := congrArg coordinates h
    have hx : a=0 := congrArg Prod.fst (Option.some.inj hh)
    exact ha hx
  · have hh := congrArg coordinates h
    have hx : a=n := congrArg Prod.fst (Option.some.inj hh)
    exact ham (sub_eq_zero.mpr hx)
  · have hh := congrArg coordinates h
    have hx : a= -n := congrArg Prod.fst (Option.some.inj hh)
    apply hap
    simp [hx]

/-- The formal-neighborhood remainder of a complete source is genuinely finite;
this discharges the point-at-infinity exception before introducing coordinates. -/
theorem source_remainder_coordinates {n : ℤ} (hn : n ≠ 0) {a b : ℚ}
    (hQ : CongruentEquation (n:ℚ) a b)
    (ha : a ≠ 0) (ham : a-n ≠ 0) (hap : a+n ≠ 0)
    (U τ : Point (n:ℚ)) (hU : U ∈ H n hn) (ht : 2 • τ=0)
    (hQU : finitePoint (by exact_mod_cast hn) hQ=U+τ) :
    ∃ x y : ℚ, ∃ hE : CongruentEquation (n:ℚ) x y,
      U=finitePoint (by exact_mod_cast hn) hE ∧ padicValRat 2 x ≤ -4 := by
  have hu0 : U ≠ 0 := by
    intro hu
    have hqt : finitePoint (by exact_mod_cast hn) hQ=τ := by simpa [hu] using hQU
    exact finite_source_not_two_torsion (by exact_mod_cast hn) hQ ha ham hap (by rw [hqt,ht])
  cases U with
  | zero => exact False.elim (hu0 rfl)
  | some x y he =>
    have heq := (congruentEquation_iff_weierstrass (n:ℚ) x y).mpr he.left
    exact ⟨x,y,heq,rfl,(some_mem_H_iff n hn x y he).mp hU⟩

/-- Formal-neighborhood coordinates carry all three nonzero slots and even
negative depth, with no additional valuation hypotheses. -/
theorem actual_H_coordinate_data {n : ℤ} (hn : n ≠ 0) {x y : ℚ}
    (hE : CongruentEquation (n:ℚ) x y)
    (hU : finitePoint (by exact_mod_cast hn) hE ∈ H n hn) :
    x ≠ 0 ∧ x-(n:ℚ) ≠ 0 ∧ x+(n:ℚ) ≠ 0 ∧
    (x:ℚ_[2]).valuation < 0 ∧ Even (x:ℚ_[2]).valuation := by
  have hv := (some_mem_H_iff n hn x y (nonsingular (by exact_mod_cast hn) hE)).mp hU
  let P := commonSourceDyadicOfRat n x y hE hv
  have hnrm := Padic.norm_int_le_one (p:=2) n
  have h0 := P.x_ne_zero
  have hm := (P.offsets_ne_zero hnrm).1
  have hp := (P.offsets_ne_zero hnrm).2
  have hs := (P.local_squares hnrm).1
  refine ⟨?_,?_,?_,?_,commonRoot_even_val_of_isSquare hs⟩
  · intro h
    apply h0
    change (x:ℚ_[2])=0
    exact_mod_cast h
  · intro h
    apply hm
    change (x:ℚ_[2])-(n:ℚ_[2])=0
    exact_mod_cast h
  · intro h
    apply hp
    change (x:ℚ_[2])+(n:ℚ_[2])=0
    exact_mod_cast h
  · rw [Padic.valuation_ratCast]
    omega

/-- For both admissible dyadic residue classes, the actual complete ordered
source and even valuation of the literal return force equal remainder depths.
The label disjunction and all coordinate parity conditions are derived. -/
theorem actual_source_even_return_same_depth {n : ℤ} (hn : n ≠ 0)
    (hn8 : n%8=1 ∨ n%8=7) {a b c e u v x y w z : ℚ}
    (hQ : CongruentEquation (n:ℚ) a b) (hR : CongruentEquation (n:ℚ) c e)
    (hU : CongruentEquation (n:ℚ) x y) (hV : CongruentEquation (n:ℚ) w z)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u^2= -(a*c)/n) (hv : v^2= -((a-n)*(c-n))/n)
    (hUH : finitePoint (by exact_mod_cast hn) hU ∈ H n hn)
    (hVH : finitePoint (by exact_mod_cast hn) hV ∈ H n hn)
    (τQ τR : Point (n:ℚ)) (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hQU : finitePoint (by exact_mod_cast hn) hQ=finitePoint (by exact_mod_cast hn) hU+τQ)
    (hRV : finitePoint (by exact_mod_cast hn) hR=finitePoint (by exact_mod_cast hn) hV+τR)
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation) :
    padicValRat 2 x=padicValRat 2 w := by
  obtain ⟨hx,hxm,hxp,hxv,hxe⟩ := actual_H_coordinate_data hn hU hUH
  obtain ⟨hw,hwm,hwp,hwv,hwe⟩ := actual_H_coordinate_data hn hV hVH
  have hodd : Odd n := by
    rcases hn8 with h | h
    · exact Int.odd_iff.mpr (by omega)
    · exact Int.odd_iff.mpr (by omega)
  obtain ⟨hn2,hvn⟩ := commonSource_dyadic_odd_int_unit hodd
  have hs := source_kummer_sum (by exact_mod_cast hn) hQ hR ha hc ham hcm hap hcp hu hv
  have hev : (x:ℚ_[2]).valuation=(w:ℚ_[2]).valuation := by
    rcases hn8 with h | h
    · have ht := source_torsion_sum_one n hn h _ _ _ _ τQ τR hUH hVH hQU hRV htQ htR hs
      have ho := actual_coordinate_orders_one (by exact_mod_cast hn) hQ hR hU hV
        hx hxm hxp hw hwm hwp τQ τR htQ ht hQU hRV
      exact commonSource_dyadic_orders_one_same_val hn2 hvn hxv hwv hxe hwe ho hf
    · have ht := source_torsion_sum_seven n hn h _ _ _ _ τQ τR hUH hVH hQU hRV htQ htR hs
      have ho := actual_coordinate_orders_seven (by exact_mod_cast hn) hQ hR hU hV
        hx hxm hxp hw hwm hwp τQ τR htQ ht hQU hRV
      exact commonSource_dyadic_orders_seven_same_val hn2 hvn hxv hwv hxe hwe ho hf
  simpa only [Padic.valuation_ratCast] using hev

#print axioms source_remainder_coordinates
#print axioms actual_H_coordinate_data
#print axioms actual_source_even_return_same_depth
end FourCorner.CommonSource
