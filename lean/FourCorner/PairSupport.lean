import FourCorner.GaussianCorners
import FourCorner.PairIdentity
import FourCorner.PairOppositeSquare
import FourCorner.PairUnramified
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace FourCorner

/-- Cancellation of the actual norm signs at a prime dividing the side.
This is a field calculation; no extension-field Frobenius computation is needed. -/
lemma gaussian_equal_displacements_opposite_norms
    {F : Type*} [Field F] (h2 : (2:F) ≠ 0)
    (mi mj a b c d : F)
    (hr : mi*(a^2-b^2)=mj*(c^2-d^2))
    (hn : mi*(a^2+b^2)+mj*(c^2+d^2)=0)
    (hj : c ≠ 0 ∨ d ≠ 0) : IsSquare (-mi*mj) := by
  have hr1 : mi*a^2 + mj*d^2 = 0 := by
    have hh : 2*(mi*a^2+mj*d^2)=0 := by linear_combination hr + hn
    exact (mul_eq_zero.mp hh).resolve_left h2
  have hr2 : mi*b^2 + mj*c^2 = 0 := by
    have hh : 2*(mi*b^2+mj*c^2)=0 := by linear_combination hn - hr
    exact (mul_eq_zero.mp hh).resolve_left h2
  rcases hj with hc | hd
  · refine ⟨mi*b/c, ?_⟩
    field_simp
    linear_combination -mi * hr2
  · refine ⟨mi*a/d, ?_⟩
    field_simp
    linear_combination -mi * hr1

lemma square_of_pair_identity {F : Type*} [Field F] (h2 : (2:F) ≠ 0)
    (s d L R : F) (hL : L ≠ 0) (hd : d ≠ 0) (hsq : IsSquare d)
    (heq : -4*s*R^2=d*L^2) : IsSquare (-s) := by
  have hR : R ≠ 0 := by
    intro hz
    have hh : d*L^2=0 := by simpa [hz] using heq.symm
    exact (mul_ne_zero hd (pow_ne_zero 2 hL)) hh
  obtain ⟨t,ht⟩ := hsq
  refine ⟨t*L/(2*R),?_⟩
  field_simp
  rw [ht] at heq
  linear_combination heq

namespace IntegralModel

lemma corner_radius_odd (M : IntegralModel) (c : Bool × Bool) : Odd (M.cornerRadius c) := by
  obtain ⟨_,_,h0,h1,h2,h3⟩ := M.four_divides_L_and_orientation
  rcases c with ⟨e,f⟩
  cases e <;> cases f <;> simp only [cornerRadius] <;>
    apply Int.odd_iff.mpr <;> assumption

/-- The positive Gaussian norm fixes the integer radius modulo four. -/
lemma cornerRadius_mod_four (M : IntegralModel) (hX : Odd M.X) (c : Bool × Bool) :
    M.cornerRadius c % 4 = (M.cornerClass c : ℤ) % 4 := by
  have hLe : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨q,_,_,hn,_⟩ := M.corner_gaussian_root hX hLe c
  have hm : (M.cornerClass c : ℤ)%2=1 := by
    apply Int.odd_iff.mp
    exact_mod_cast M.cornerClass_odd hX hLe c
  have ha := Int.odd_iff.mp (M.corner_radius_odd c)
  have hh := congrArg (fun z : ℤ => z%2) hn
  rw [Int.mul_emod,hm,ha] at hh
  have hnorm2 : Zsqrtd.norm q%2=1 := by omega
  have hnorm4 : Zsqrtd.norm q%4=1 := by
    have a0 := Int.emod_nonneg q.re (by norm_num : (4:ℤ)≠0)
    have a1 := Int.emod_lt_of_pos q.re (by norm_num : (0:ℤ)<4)
    have b0 := Int.emod_nonneg q.im (by norm_num : (4:ℤ)≠0)
    have b1 := Int.emod_lt_of_pos q.im (by norm_num : (0:ℤ)<4)
    have hn4 : Zsqrtd.norm q%4=(q.re%4*q.re%4+q.im%4*q.im%4)%4 := by
      simp [Zsqrtd.norm,Int.add_emod,Int.mul_emod]
    interval_cases hr : q.re%4 <;> interval_cases hi : q.im%4 <;>
      norm_num [hr,hi] at hn4 <;> omega
  rw [hn,Int.mul_emod,hnorm4,mul_one,Int.emod_emod]

lemma corner_pair_half_sum_integral (M : IntegralModel) (c d : Bool × Bool) :
    2 * ((M.cornerRadius c + M.cornerRadius d) / 2) = M.cornerRadius c + M.cornerRadius d := by
  apply Int.mul_ediv_cancel'
  exact even_iff_two_dvd.mp ((M.corner_radius_odd c).add_odd (M.corner_radius_odd d))

lemma corner_pair_half_sum_positive (M : IntegralModel) (c d : Bool × Bool) :
    0 < (M.cornerRadius c + M.cornerRadius d) / 2 := by
  have h := M.corner_pair_half_sum_integral c d
  have hc := M.cornerRadius_pos c
  have hd := M.cornerRadius_pos d
  omega

/-- At a prime dividing the side, the full signed Gaussian norm equations
force the negative pair class to be a square whenever the two radii cancel. -/
lemma pair_square_at_side_prime (M : IntegralModel) (hX : Odd M.X)
    (c d : Bool × Bool) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : (M.L : ZMod p) = 0)
    (hs : ((M.cornerRadius c : ℤ) : ZMod p) + M.cornerRadius d = 0) :
    IsSquare (-((M.cornerClass c : ℕ) : ZMod p) * M.cornerClass d) := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hLe : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨qi,_,hri,hni,_⟩ := M.corner_gaussian_root hX hLe c
  obtain ⟨qj,_,hrj,hnj,_⟩ := M.corner_gaussian_root hX hLe d
  have cx (e : Bool) : ((M.cornerX e : ℤ) : ZMod p) = M.X := by
    cases e <;> simp [cornerX,hL]
  have cy (e : Bool) : ((M.cornerY e : ℤ) : ZMod p) = M.Y := by
    cases e <;> simp [cornerY,hL]
  have ri : (M.X : ZMod p) = M.cornerClass c * ((qi.re : ZMod p)^2-(qi.im : ZMod p)^2) := by
    have hh := congrArg Zsqrtd.re hri
    simp [pow_two,Zsqrtd.re_mul,Zsqrtd.im_mul] at hh
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hh
    simpa [cx,pow_two,sub_eq_add_neg] using hc
  have rj : (M.X : ZMod p) = M.cornerClass d * ((qj.re : ZMod p)^2-(qj.im : ZMod p)^2) := by
    have hh := congrArg Zsqrtd.re hrj
    simp [pow_two,Zsqrtd.re_mul,Zsqrtd.im_mul] at hh
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hh
    simpa [cx,pow_two,sub_eq_add_neg] using hc
  have ij : (M.Y : ZMod p) = M.cornerClass d * (2*(qj.re : ZMod p)*(qj.im : ZMod p)) := by
    have hh := congrArg Zsqrtd.im hrj
    simp [pow_two,Zsqrtd.re_mul,Zsqrtd.im_mul] at hh
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hh
    simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast,cy] at hc
    linear_combination hc
  have ni : ((M.cornerRadius c : ℤ) : ZMod p) =
      M.cornerClass c * ((qi.re : ZMod p)^2+(qi.im : ZMod p)^2) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod p)) hni
    simpa [Zsqrtd.norm,pow_two] using hh
  have nj : ((M.cornerRadius d : ℤ) : ZMod p) =
      M.cornerClass d * ((qj.re : ZMod p)^2+(qj.im : ZMod p)^2) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod p)) hnj
    simpa [Zsqrtd.norm,pow_two] using hh
  have hj : (qj.re : ZMod p) ≠ 0 ∨ (qj.im : ZMod p) ≠ 0 := by
    by_contra hn
    push Not at hn
    have hx0 : (M.X : ZMod p) = 0 := by simpa [hn.1,hn.2] using rj
    have hy0 : (M.Y : ZMod p) = 0 := by simpa [hn.1,hn.2] using ij
    have hh := M.common_divisor_eq_one
      ((ZMod.intCast_zmod_eq_zero_iff_dvd M.X p).mp hx0)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd M.Y p).mp hy0)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mp hL)
    exact hp.ne_one hh
  apply gaussian_equal_displacements_opposite_norms h2 _ _
    (qi.re : ZMod p) (qi.im : ZMod p) (qj.re : ZMod p) (qj.im : ZMod p)
  · exact ri.symm.trans rj
  · rw [← ni,← nj]
    exact hs
  · exact hj

lemma pair_square_away_from_side (M : IntegralModel) (hX : Odd M.X)
    (c d : Bool × Bool) (hne : c ≠ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : (M.L : ZMod p) ≠ 0)
    (hs : ((M.cornerRadius c : ℤ) : ZMod p) + M.cornerRadius d = 0) :
    IsSquare (-((M.cornerClass c : ℕ) : ZMod p) * M.cornerClass d) := by
  let : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hd0 : (cornerDistanceSquared c d : ZMod p) ≠ 0 := by
    rcases cornerDistanceSquared_one_or_two hne with hd | hd
    · rw [hd]; norm_num
    · simpa [hd] using h2
  have hdsq : IsSquare (cornerDistanceSquared c d : ZMod p) := by
    rcases cornerDistanceSquared_one_or_two hne with hd | hd
    · rw [hd]; exact ⟨1,by norm_num⟩
    · have hop : c.1 ≠ d.1 ∧ c.2 ≠ d.2 := by
        rcases c with ⟨ce,cf⟩
        rcases d with ⟨de,df⟩
        cases ce <;> cases cf <;> cases de <;> cases df <;>
          norm_num [cornerDistanceSquared] at hd <;> decide
      rw [hd]
      norm_num only [Int.cast_ofNat]
      apply M.opposite_radius_sum_isSquare_two hp hp2
        (fun hl => hL ((ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mpr hl)) hop.1 hop.2
      simpa using hs
  have hLe : Even M.L := even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨qi,_,hri,hni,_⟩ := M.corner_gaussian_root hX hLe c
  obtain ⟨qj,_,hrj,hnj,_⟩ := M.corner_gaussian_root hX hLe d
  have hi := M.corner_pair_identity c d qi qj hri hrj hni hnj
  have hi' : -4*((M.cornerClass c : ZMod p)*M.cornerClass d)*
      ((qi*star qj).re : ZMod p)^2=(cornerDistanceSquared c d : ZMod p)*(M.L:ZMod p)^2 := by
    have hh := congrArg (fun z : ℤ => (z : ZMod p)) hi
    simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      Int.cast_ofNat,hs,zero_pow (by decide : 2 ≠ 0),zero_sub] at hh
    linear_combination hh
  simpa only [neg_mul] using square_of_pair_identity h2
    ((M.cornerClass c : ZMod p)*M.cornerClass d) (cornerDistanceSquared c d : ZMod p)
    (M.L:ZMod p) ((qi*star qj).re : ZMod p) hL hd0 hdsq hi'

/-- Every odd prime in any actual radius pair sum is unramified and split
in the negative product of the two canonical corner classes. -/
theorem pair_sum_prime_support (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hs : (p:ℤ) ∣ M.cornerRadius c+M.cornerRadius d) :
    (¬ p ∣ M.cornerClass c*M.cornerClass d) ∧
    legendreSym p (-((M.cornerClass c : ℤ)*M.cornerClass d)) = 1 := by
  have hp : p.Prime := Fact.out
  have hu := M.pair_sum_prime_not_dvd_cornerClasses hne hp hp2 hs
  refine ⟨hu,?_⟩
  have hprod : ((M.cornerClass c : ZMod p)*M.cornerClass d) ≠ 0 := by
    intro hh
    apply hu
    apply (ZMod.natCast_eq_zero_iff (M.cornerClass c*M.cornerClass d) p).mp
    simpa only [Nat.cast_mul] using hh
  have hns : ((-((M.cornerClass c : ℤ)*M.cornerClass d) : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_neg,Int.cast_mul,Int.cast_natCast,neg_ne_zero] using hprod
  apply (legendreSym.eq_one_iff p hns).mpr
  have hs0 : ((M.cornerRadius c : ℤ) : ZMod p)+M.cornerRadius d=0 := by
    simpa only [Int.cast_add] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (M.cornerRadius c+M.cornerRadius d) p).mpr hs
  by_cases hL : (M.L : ZMod p)=0
  · simpa only [Int.cast_neg,Int.cast_mul,Int.cast_natCast,neg_mul] using
      M.pair_square_at_side_prime hX c d hp hp2 hL hs0
  · simpa only [Int.cast_neg,Int.cast_mul,Int.cast_natCast,neg_mul] using
      M.pair_square_away_from_side hX c d hne hp hp2 hL hs0

/-- Manuscript theorem `profile-six-pair-support`, with the actual positive
integer half-sum and the actual canonical squarefree corner classes. -/
theorem six_pair_support (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (hne : c ≠ d) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hV : (p:ℤ) ∣ (M.cornerRadius c+M.cornerRadius d)/2) :
    (¬ p ∣ M.cornerClass c*M.cornerClass d) ∧
    legendreSym p (-((M.cornerClass c : ℤ)*M.cornerClass d)) = 1 := by
  apply M.pair_sum_prime_support hX hne hp2
  rw [← M.corner_pair_half_sum_integral c d]
  exact dvd_mul_of_dvd_right hV 2

end IntegralModel
end FourCorner
#print axioms FourCorner.gaussian_equal_displacements_opposite_norms
#print axioms FourCorner.IntegralModel.pair_square_at_side_prime

#print axioms FourCorner.IntegralModel.pair_square_away_from_side

#print axioms FourCorner.IntegralModel.cornerRadius_mod_four
#print axioms FourCorner.IntegralModel.six_pair_support
