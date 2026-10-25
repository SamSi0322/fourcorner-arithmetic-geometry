import FourCorner.PairSupport
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

set_option autoImplicit false

namespace FourCorner.IntegralModel

/-- The actual positive half-sum of two corner radii, regarded as a natural number. -/
def pairHalfSumNat (M : IntegralModel) (c d : Bool × Bool) : ℕ :=
  ((M.cornerRadius c + M.cornerRadius d) / 2).toNat

lemma pairHalfSumNat_pos (M : IntegralModel) (c d : Bool × Bool) :
    0 < M.pairHalfSumNat c d := by
  exact Int.pos_iff_toNat_pos.mp (M.corner_pair_half_sum_positive c d)

@[simp] lemma pairHalfSumNat_cast (M : IntegralModel) (c d : Bool × Bool) :
    (M.pairHalfSumNat c d : ℤ) = (M.cornerRadius c + M.cornerRadius d) / 2 := by
  exact Int.toNat_of_nonneg (le_of_lt (M.corner_pair_half_sum_positive c d))

lemma pairHalfSumNat_symm (M : IntegralModel) (c d : Bool × Bool) :
    M.pairHalfSumNat c d = M.pairHalfSumNat d c := by
  simp only [pairHalfSumNat, add_comm]

lemma pairHalfSumNat_jacobi_support (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hdiv : p ∣ M.pairHalfSumNat c d) :
    jacobiSym (-((M.cornerClass c * M.cornerClass d : ℕ) : ℤ)) p = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hodd.ne_two_of_dvd_nat (dvd_refl p)
  have hdivInt : (p : ℤ) ∣ (M.cornerRadius c + M.cornerRadius d) / 2 := by
    rw [← M.pairHalfSumNat_cast c d]
    exact Int.natCast_dvd_natCast.mpr hdiv
  have hs := (M.six_pair_support hX hne hp2 hdivInt).2
  rw [jacobiSym.legendreSym.to_jacobiSym] at hs
  simpa only [Nat.cast_mul] using hs

lemma cornerDistanceSquared_symm (c d : Bool × Bool) :
    cornerDistanceSquared c d = cornerDistanceSquared d c := by
  simp only [cornerDistanceSquared]
  ring

lemma cornerDistanceSquared_toNat_sub_one (c d : Bool × Bool) :
    (cornerDistanceSquared c d).toNat - 1 = (cornerDistanceSquared c d - 1).toNat := by
  omega

end FourCorner.IntegralModel

#print axioms FourCorner.IntegralModel.pairHalfSumNat_jacobi_support
