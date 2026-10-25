import FourCorner.GaussianCorners
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.NatPrime

set_option autoImplicit false

namespace FourCorner
namespace IntegralModel

/-- The canonical squarefree corner multiplier divides the actual content. -/
theorem cornerClass_dvd_cornerContent (M : IntegralModel) (c : Bool × Bool) :
    M.cornerClass c ∣ M.cornerContent c := squarefreePart_dvd _

/-- The canonical multiplier divides the signed horizontal corner leg. -/
theorem cornerClass_dvd_cornerX (M : IntegralModel) (c : Bool × Bool) :
    (M.cornerClass c : ℤ) ∣ M.cornerX c.1 :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (M.cornerClass_dvd_cornerContent c))
    (M.cornerContent_dvd_X c)

/-- The canonical multiplier divides the signed vertical corner leg. -/
theorem cornerClass_dvd_cornerY (M : IntegralModel) (c : Bool × Bool) :
    (M.cornerClass c : ℤ) ∣ M.cornerY c.2 :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (M.cornerClass_dvd_cornerContent c))
    (M.cornerContent_dvd_Y c)

/-- The canonical multiplier divides the positive radius in the original
integer model, already by the Pythagorean equation at that corner. -/
theorem cornerClass_dvd_cornerRadius (M : IntegralModel) (c : Bool × Bool) :
    (M.cornerClass c : ℤ) ∣ M.cornerRadius c := by
  have ht : PythagoreanTriple (M.cornerX c.1) (M.cornerY c.2) (M.cornerRadius c) := by
    unfold PythagoreanTriple
    nlinarith [M.corner_sq c]
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (M.cornerClass_dvd_cornerContent c))
    ht.gcd_dvd

/-- If an odd prime annihilates both legs at one corner and the radius at
a distinct corner, it divides the original square side. -/
theorem corner_legs_other_radius_prime_dvd_side (M : IntegralModel) {c d : Bool × Bool} (hne : c ≠ d)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hx : (p : ℤ) ∣ M.cornerX c.1)
    (hy : (p : ℤ) ∣ M.cornerY c.2)
    (hr : (p : ℤ) ∣ M.cornerRadius d) : (p : ℤ) ∣ M.L := by
  let : Fact p.Prime := ⟨hp⟩
  have hx0 : (M.cornerX c.1 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
  have hy0 : (M.cornerY c.2 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
  have hr0 : (M.cornerRadius d : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr
  have hs : (M.cornerRadius d : ZMod p) ^ 2 =
      (M.cornerX d.1 : ZMod p) ^ 2 + (M.cornerY d.2 : ZMod p) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add] using
      congrArg (fun z : ℤ => (z : ZMod p)) (M.corner_sq d)
  rw [hr0, zero_pow (by decide : 2 ≠ 0)] at hs
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (Nat.dvd_prime Nat.prime_two).mp hpd |>.elim hp.ne_one hp2
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rcases c with ⟨e, h⟩
  rcases d with ⟨e', h'⟩
  cases e <;> cases h <;> cases e' <;> cases h' <;>
    try exact (hne rfl).elim
  all_goals
    simp only [cornerX, cornerY, Bool.false_eq_true, ↓reduceIte, sub_zero,
      Int.cast_sub, sub_eq_zero] at hx0 hy0 hs
    simp only [hx0, hy0, sub_self, zero_sub, neg_sq,
      zero_pow (by decide : 2 ≠ 0), zero_add, add_zero] at hs
    ring_nf at hs
    simpa only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), htwo, or_false] using hs.symm

/-- A prime in a pair sum cannot divide the canonical class at the first
corner: that would force the primitive side and both corner legs to vanish. -/
theorem pair_sum_prime_not_dvd_cornerClass_left (M : IntegralModel)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : (p : ℤ) ∣ M.cornerRadius c + M.cornerRadius d) :
    ¬ p ∣ M.cornerClass c := by
  intro hc
  have hci : (p : ℤ) ∣ (M.cornerClass c : ℤ) := Int.natCast_dvd_natCast.mpr hc
  have hx := dvd_trans hci (M.cornerClass_dvd_cornerX c)
  have hy := dvd_trans hci (M.cornerClass_dvd_cornerY c)
  have hrc := dvd_trans hci (M.cornerClass_dvd_cornerRadius c)
  have hrd : (p : ℤ) ∣ M.cornerRadius d := by
    simpa only [add_sub_cancel_left] using dvd_sub hs hrc
  have hl := M.corner_legs_other_radius_prime_dvd_side hne hp hp2 hx hy hrd
  exact hp.ne_one (M.common_corner_divisor_eq_one c hx hy hl)

/-- Every odd prime in the actual sum of two distinct corner radii is
unramified in the product of their canonical squarefree corner classes. -/
theorem pair_sum_prime_not_dvd_cornerClasses (M : IntegralModel)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : (p : ℤ) ∣ M.cornerRadius c + M.cornerRadius d) :
    ¬ p ∣ M.cornerClass c * M.cornerClass d := by
  intro hd
  rcases hp.dvd_mul.mp hd with hc | hd
  · exact M.pair_sum_prime_not_dvd_cornerClass_left hne hp hp2 hs hc
  · exact M.pair_sum_prime_not_dvd_cornerClass_left hne.symm hp hp2
      (by simpa only [add_comm] using hs) hd

/-- Integer divisibility form of the pair-sum unramifiedness theorem. -/
theorem pair_sum_prime_not_dvd_cornerClasses_int (M : IntegralModel)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hs : (p : ℤ) ∣ M.cornerRadius c + M.cornerRadius d) :
    ¬ (p : ℤ) ∣ (M.cornerClass c : ℤ) * (M.cornerClass d : ℤ) := by
  intro hd
  apply M.pair_sum_prime_not_dvd_cornerClasses hne hp hp2 hs
  exact_mod_cast hd

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.cornerClass_dvd_cornerRadius

#print axioms FourCorner.IntegralModel.corner_legs_other_radius_prime_dvd_side
#print axioms FourCorner.IntegralModel.pair_sum_prime_not_dvd_cornerClasses
#print axioms FourCorner.IntegralModel.pair_sum_prime_not_dvd_cornerClasses_int
