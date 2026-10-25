import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FourCorner.NineThreeHPlus

private lemma square_mod_sixteen (x : ℤ) :
    x ^ 2 % 16 = 0 ∨ x ^ 2 % 16 = 1 ∨ x ^ 2 % 16 = 4 ∨ x ^ 2 % 16 = 9 := by
  have hlo := Int.emod_nonneg x (by norm_num : (16 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 16)
  interval_cases hx : x % 16 <;> norm_num [pow_two, Int.mul_emod, hx]

private lemma square_mod_two (x : ℤ) : x ^ 2 % 2 = x % 2 := by
  have hlo := Int.emod_nonneg x (by norm_num : (2 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 2)
  interval_cases hx : x % 2 <;> norm_num [pow_two, Int.mul_emod, hx]

/-- The quartic equation forces both homogeneous coordinates to be even.
The proof uses the four square residues modulo sixteen. -/
theorem quartic_forces_even (U V W : ℤ)
    (heq : 2 * W ^ 2 = 3 * V ^ 4 + 2 * U ^ 2 * V ^ 2 - U ^ 4) :
    U % 2 = 0 ∧ V % 2 = 0 := by
  have su := square_mod_sixteen U
  have sv := square_mod_sixteen V
  have sw := square_mod_sixteen W
  have pu := square_mod_two U
  have pv := square_mod_two V
  rw [show U ^ 4 = U ^ 2 * U ^ 2 by ring,
    show V ^ 4 = V ^ 2 * V ^ 2 by ring] at heq
  have hm := congrArg (fun z : ℤ => z % 16) heq
  simp only [Int.sub_emod, Int.add_emod, Int.mul_emod, Int.emod_emod] at hm
  rcases su with su | su | su | su <;>
    rcases sv with sv | sv | sv | sv <;>
    rcases sw with sw | sw | sw | sw <;>
    norm_num [su, sv, sw] at hm <;> omega

/-- The dyadic quartic has no primitive integer solution. -/
theorem primitive_quartic_impossible (U V W : ℤ)
    (hprim : Nat.Coprime U.natAbs V.natAbs) :
    2 * W ^ 2 ≠ 3 * V ^ 4 + 2 * U ^ 2 * V ^ 2 - U ^ 4 := by
  intro heq
  obtain ⟨hu, hv⟩ := quartic_forces_even U V W heq
  have hu' : 2 ∣ U.natAbs := Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero hu)
  have hv' : 2 ∣ V.natAbs := Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero hv)
  have hd : 2 ∣ Nat.gcd U.natAbs V.natAbs := Nat.dvd_gcd hu' hv'
  rw [hprim.gcd_eq_one] at hd
  norm_num at hd

end FourCorner.NineThreeHPlus

#print axioms FourCorner.NineThreeHPlus.quartic_forces_even
#print axioms FourCorner.NineThreeHPlus.primitive_quartic_impossible
