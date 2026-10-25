import FourCorner.CornerReciprocityOne
import FourCorner.CornerReciprocitySeven
import FourCorner.ReciprocitySigma16
import FourCorner.PairHalfSum
import FourCorner.CornerReciprocityJacobi

set_option autoImplicit false

namespace FourCorner
namespace IntegralModel

private lemma actual_corner_prime_support (M : IntegralModel)
    (i : Bool × Bool) {p : ℕ} (hp : p.Prime) (hdiv : p ∣ M.cornerClass i) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  obtain ⟨hL, hXY⟩ := M.basic_mod_four
  exact M.cornerClass_prime_support (Int.dvd_of_emod_eq_zero hL) (by omega) i hp hdiv

/-- Manuscript Lemma `profile-ramified-character`, combining both possible
prime residue classes on the canonical support of a corner. -/
theorem corner_ramified_character (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] {i j : Bool × Bool} (hne : i ≠ j)
    (hdiv : p ∣ M.cornerClass i) :
    legendreSym p ((M.cornerRadius i + M.cornerRadius j) / 2) =
      legendreSym p (M.cornerClass j) *
        sigma16 p ^ ((cornerDistanceSquared i j - 1).toNat) := by
  rcases M.actual_corner_prime_support i Fact.out hdiv with hp | hp
  · rw [sigma16_of_mod_eight_eq_one hp]
    exact M.corner_ramified_character_one hX hp hne hdiv
  · rw [sigma16_of_mod_eight_eq_seven hp]
    exact M.corner_ramified_character_seven hX hp hne hdiv

/-- The full ramified character in the positive natural half-sum convention
used by Jacobi reciprocity. -/
theorem pairHalfSumNat_ramified_character (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] {i j : Bool × Bool} (hne : i ≠ j)
    (hdiv : p ∣ M.cornerClass i) :
    jacobiSym (M.pairHalfSumNat i j : ℤ) p =
      jacobiSym (M.cornerClass j : ℤ) p *
        sigma16 p ^ ((cornerDistanceSquared i j - 1).toNat) := by
  rw [M.pairHalfSumNat_cast]
  simpa only [jacobiSym.legendreSym.to_jacobiSym] using
    M.corner_ramified_character hX hne hdiv

/-- Manuscript Theorem `profile-master`, for every pair of distinct original
corners. All support and local character conditions are derived from the
actual primitive integral model and its canonical squarefree corner classes. -/
theorem actual_pair_reciprocity (M : IntegralModel) (hX : Odd M.X)
    {i j : Bool × Bool} (hne : i ≠ j) :
    oddPartChar (M.pairHalfSumNat i j) ^ (1 + e4 (M.cornerClass i * M.cornerClass j)) =
      (-1 : ℤ) ^ (e4 (M.cornerClass i) * e4 (M.cornerClass j)) *
        sigma16 (M.cornerClass i * M.cornerClass j) ^
          ((cornerDistanceSquared i j - 1).toNat) := by
  have hLe : Even M.L := even_iff_two_dvd.mpr
    (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  have hrami : ∀ p : ℕ, p.Prime → p ∣ M.cornerClass i →
      jacobiSym (M.pairHalfSumNat i j : ℤ) p =
        jacobiSym (M.cornerClass j : ℤ) p *
          sigma16 p ^ ((cornerDistanceSquared i j).toNat - 1) := by
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    rw [cornerDistanceSquared_toNat_sub_one]
    exact M.pairHalfSumNat_ramified_character hX hne hd
  have hramj : ∀ p : ℕ, p.Prime → p ∣ M.cornerClass j →
      jacobiSym (M.pairHalfSumNat i j : ℤ) p =
        jacobiSym (M.cornerClass i : ℤ) p *
          sigma16 p ^ ((cornerDistanceSquared i j).toNat - 1) := by
    intro p hp hd
    let : Fact p.Prime := ⟨hp⟩
    rw [cornerDistanceSquared_toNat_sub_one, M.pairHalfSumNat_symm i j,
      cornerDistanceSquared_symm i j]
    exact M.pairHalfSumNat_ramified_character hX hne.symm hd
  have hm := pair_reciprocity_master
    (d := (cornerDistanceSquared i j).toNat)
    (M.cornerClass_odd hX hLe i) (M.cornerClass_odd hX hLe j)
    (M.cornerClass_squarefree i) (M.cornerClass_squarefree j)
    (M.cornerClass_pairwise_coprime hne) (M.pairHalfSumNat_pos i j)
    (fun p hp hd => M.actual_corner_prime_support i hp hd)
    (fun p hp hd => M.actual_corner_prime_support j hp hd)
    (fun p hp hodd hd => M.pairHalfSumNat_jacobi_support hX hne hp hodd hd)
    hrami hramj
  simpa only [cornerDistanceSquared_toNat_sub_one] using hm

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.corner_ramified_character

#print axioms FourCorner.IntegralModel.pairHalfSumNat_ramified_character
#print axioms FourCorner.IntegralModel.actual_pair_reciprocity
