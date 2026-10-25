import FourCorner.PairSupport
import FourCorner.CornerReciprocityActual
import FourCorner.GaussianKernel
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
namespace FourCorner

/-- The 2-adic content of an opposite radius difference, expressed entirely
as an integer divisibility statement. -/
lemma half_sum_mod_four_of_square_difference {a b : ℤ}
    (_ha : Odd a) (hb : Odd b) (hmod : a%4=b%4)
    (hsq : (16:ℤ) ∣ a^2-b^2) : (a+b)/2%4=a%4 := by
  have hab4 : (4:ℤ) ∣ a-b := Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨k,hk⟩ := hab4
  obtain ⟨t,ht⟩ := hsq
  have ha' : a=b+4*k := by omega
  have hprod : k*(b+2*k)=2*t := by
    rw [ha'] at ht
    nlinarith [ht]
  have hk2 : (2:ℤ) ∣ k := by
    have hp : (2:ℤ) ∣ k*(b+2*k) := ⟨t,hprod⟩
    rcases Int.prime_two.dvd_or_dvd hp with h | h
    · exact h
    · have hb2 := Int.odd_iff.mp hb
      have hzero := Int.emod_eq_zero_of_dvd h
      omega
  obtain ⟨u,hu⟩ := hk2
  omega

lemma nat_mod_eight_eq_one_of_prime_divisors (n : ℕ) (hn : n ≠ 0)
    (hs : ∀ p:ℕ, p.Prime → p ∣ n → p%8=1) : n%8=1 := by
  have aux : ∀ n:ℕ, n≠0 → (∀ p:ℕ,p.Prime→p∣n→p%8=1) → n%8=1 := by
    apply induction_on_primes
    · intro h
      exact (h rfl).elim
    · intro _ _
      norm_num
    · intro p a hp ih hpa hs
      have ha : a≠0 := by intro h; simp [h] at hpa
      have hpm := hs p hp (dvd_mul_right p a)
      have ham := ih ha (fun q hq hqa => hs q hq (dvd_mul_of_dvd_right hqa p))
      norm_num [Nat.mul_mod,hpm,ham]
  exact aux n hn hs

namespace IntegralModel

lemma cornerClass_mod_eight (M : IntegralModel) (c : Bool × Bool) :
    M.cornerClass c%8=1 ∨ M.cornerClass c%8=7 := by
  have hb := M.basic_mod_four
  exact nat_mod_eight_of_prime_divisors (M.cornerClass c)
    (Nat.ne_of_gt (M.cornerClass_pos c))
    (fun p hp hd => M.cornerClass_prime_support
      (Int.dvd_of_emod_eq_zero hb.1) (by omega) c hp hd)

lemma pairColour_mod_eight (M : IntegralModel) (c d : Bool × Bool) :
    (M.cornerClass c*M.cornerClass d)%8=1 ∨ (M.cornerClass c*M.cornerClass d)%8=7 := by
  rcases M.cornerClass_mod_eight c with hc | hc <;>
    rcases M.cornerClass_mod_eight d with hd | hd <;>
    norm_num [Nat.mul_mod,hc,hd]

lemma opposite_radius_square_difference_sixteen (M : IntegralModel)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    (16:ℤ) ∣ M.cornerRadius c^2 - M.cornerRadius d^2 := by
  have hL : (8:ℤ) ∣ M.L := Int.dvd_of_emod_eq_zero M.eight_divides_L
  obtain ⟨k,hk⟩ := hL
  rcases c with ⟨ce,cf⟩
  rcases d with ⟨de,df⟩
  cases ce <;> cases cf <;> cases de <;> cases df <;>
    try exact (he rfl).elim
  all_goals try exact (hf rfl).elim
  all_goals
    simp only [cornerRadius]
  · refine ⟨k*(M.X+M.Y-M.L),?_⟩
    rw [M.sq₀,M.sq₃,hk]
    ring
  · refine ⟨k*(M.X-M.Y),?_⟩
    rw [M.sq₂,M.sq₁,hk]
    ring
  · refine ⟨k*(M.Y-M.X),?_⟩
    rw [M.sq₁,M.sq₂,hk]
    ring
  · refine ⟨k*(M.L-M.X-M.Y),?_⟩
    rw [M.sq₃,M.sq₀,hk]
    ring

/-- For an opposite pair whose canonical colours agree modulo four, its
positive half-sum is odd and has that same residue modulo four. -/
theorem opposite_half_sum_mod_four (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2)
    (hm : M.cornerClass c%4=M.cornerClass d%4) :
    Odd ((M.cornerRadius c+M.cornerRadius d)/2) ∧
    (M.cornerRadius c+M.cornerRadius d)/2%4=(M.cornerClass c : ℤ)%4 := by
  have hc := M.cornerRadius_mod_four hX c
  have hd := M.cornerRadius_mod_four hX d
  have hmI : (M.cornerClass c : ℤ)%4=(M.cornerClass d : ℤ)%4 := by exact_mod_cast hm
  have hv := half_sum_mod_four_of_square_difference (M.corner_radius_odd c)
    (M.corner_radius_odd d) (hc.trans (hmI.trans hd.symm))
    (M.opposite_radius_square_difference_sixteen he hf)
  refine ⟨Int.odd_iff.mpr ?_,hv.trans hc⟩
  have ha := Int.odd_iff.mp (M.corner_radius_odd c)
  omega

lemma opposite_colour_products_dvd_kernel (M : IntegralModel) :
    M.cornerClass (false,false)*M.cornerClass (true,true) ∣ M.cornerKernel ∧
    M.cornerClass (true,false)*M.cornerClass (false,true) ∣ M.cornerKernel := by
  constructor
  · refine ⟨M.cornerClass (true,false)*M.cornerClass (false,true),?_⟩
    dsimp [cornerKernel]
    ring
  · refine ⟨M.cornerClass (false,false)*M.cornerClass (true,true),?_⟩
    dsimp [cornerKernel]
    ring

lemma opposite_colour_products_split_mod_eight (M : IntegralModel)
    (hs : ∀ p:ℕ, p.Prime → p∣M.cornerKernel → p%8=1) :
    (M.cornerClass (false,false)*M.cornerClass (true,true))%8=1 ∧
    (M.cornerClass (true,false)*M.cornerClass (false,true))%8=1 := by
  have hd := M.opposite_colour_products_dvd_kernel
  constructor
  · apply nat_mod_eight_eq_one_of_prime_divisors
      _ (Nat.ne_of_gt (Nat.mul_pos (M.cornerClass_pos _) (M.cornerClass_pos _)))
    exact fun p hp hpd => hs p hp (dvd_trans hpd hd.1)
  · apply nat_mod_eight_eq_one_of_prime_divisors
      _ (Nat.ne_of_gt (Nat.mul_pos (M.cornerClass_pos _) (M.cornerClass_pos _)))
    exact fun p hp hpd => hs p hp (dvd_trans hpd hd.2)

/-- The actual opposite products have positive sigma character. Both the
odd-7 and even-7 cases follow from full pair reciprocity and the primitive
radius congruence, with no additional source assumption. -/
theorem opposite_colour_sigma_one (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    sigma16 (M.cornerClass c*M.cornerClass d)=1 := by
  have hne : c ≠ d := by intro h; exact he (congrArg Prod.fst h)
  have hdist : cornerDistanceSquared c d=2 := by
    rcases c with ⟨ce,cf⟩
    rcases d with ⟨de,df⟩
    cases ce <;> cases cf <;> cases de <;> cases df <;>
      first | exact (he rfl).elim | exact (hf rfl).elim | norm_num [cornerDistanceSquared]
  have hm := M.actual_pair_reciprocity hX hne
  norm_num only [hdist,Int.reduceSub,Int.toNat_natCast,pow_one] at hm
  have hsq := oddPartChar_sq (M.pairHalfSumNat_pos c d)
  have hc4 : M.cornerClass c%4=1 ∨ M.cornerClass c%4=3 := by
    have hh := M.cornerClass_mod_eight c
    omega
  have hd4 : M.cornerClass d%4=1 ∨ M.cornerClass d%4=3 := by
    have hh := M.cornerClass_mod_eight d
    omega
  by_cases heq : M.cornerClass c%4=M.cornerClass d%4
  · have hv := M.opposite_half_sum_mod_four hX he hf heq
    have hvodd : Odd (M.pairHalfSumNat c d) := by
      have hh : Odd (M.pairHalfSumNat c d : ℤ) := by rw [M.pairHalfSumNat_cast]; exact hv.1
      exact_mod_cast hh
    have hv4 : M.pairHalfSumNat c d%4=M.cornerClass c%4 := by
      have hh : (M.pairHalfSumNat c d : ℤ)%4=(M.cornerClass c:ℤ)%4 := by
        rw [M.pairHalfSumNat_cast]
        exact hv.2
      exact_mod_cast hh
    rw [oddPartChar_of_odd hvodd] at hm
    rcases hc4 with hc | hc <;> rcases hd4 with hd | hd <;>
      norm_num [e4,Nat.mul_mod,hc,hd,hv4] at hm <;> omega
  · rcases hc4 with hc | hc <;> rcases hd4 with hd | hd <;>
      norm_num [e4,Nat.mul_mod,hc,hd,hsq] at hm <;> omega

/-- Manuscript theorem `profile-main`: either canonical opposite product
is one or fifteen modulo sixteen. -/
theorem opposite_colour_mod_sixteen (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    (M.cornerClass c*M.cornerClass d)%16=1 ∨
    (M.cornerClass c*M.cornerClass d)%16=15 := by
  have hs := M.opposite_colour_sigma_one hX he hf
  by_contra hn
  simp [sigma16,hn] at hs

/-- The parity refinement: residue one in the even-seven case and residue
fifteen in the odd-seven case, with the parity encoded by the modulo-four
character of the canonical squarefree product. -/
theorem opposite_colour_residue_refinement (M : IntegralModel) (hX : Odd M.X)
    {c d : Bool × Bool} (he : c.1 ≠ d.1) (hf : c.2 ≠ d.2) :
    (M.cornerClass c*M.cornerClass d)%16 =
      if e4 (M.cornerClass c*M.cornerClass d)=0 then 1 else 15 := by
  rcases M.opposite_colour_mod_sixteen hX he hf with h | h
  · have h4 : (M.cornerClass c*M.cornerClass d)%4=1 := by omega
    simp [e4,h4,h]
  · have h4 : (M.cornerClass c*M.cornerClass d)%4=3 := by omega
    simp [e4,h4,h]

/-- The labelled pair of opposite-colour congruences. -/
theorem opposite_colour_congruences (M : IntegralModel) (hX : Odd M.X) :
    ((M.cornerClass (false,false)*M.cornerClass (true,true))%16=1 ∨
     (M.cornerClass (false,false)*M.cornerClass (true,true))%16=15) ∧
    ((M.cornerClass (true,false)*M.cornerClass (false,true))%16=1 ∨
     (M.cornerClass (true,false)*M.cornerClass (false,true))%16=15) := by
  exact ⟨M.opposite_colour_mod_sixteen hX (by decide) (by decide),
    M.opposite_colour_mod_sixteen hX (by decide) (by decide)⟩

/-- Manuscript corollary `profile-split`: all-split support gives residue
one modulo sixteen for both actual opposite products. -/
theorem opposite_colour_all_split (M : IntegralModel) (hX : Odd M.X)
    (hs : ∀ p:ℕ, p.Prime → p∣M.cornerKernel → p%8=1) :
    (M.cornerClass (false,false)*M.cornerClass (true,true))%16=1 ∧
    (M.cornerClass (true,false)*M.cornerClass (false,true))%16=1 := by
  have h8 := M.opposite_colour_products_split_mod_eight hs
  have h16 := M.opposite_colour_congruences hX
  omega

end IntegralModel
end FourCorner
#print axioms FourCorner.half_sum_mod_four_of_square_difference
#print axioms FourCorner.IntegralModel.opposite_half_sum_mod_four

#print axioms FourCorner.IntegralModel.opposite_colour_congruences
#print axioms FourCorner.IntegralModel.opposite_colour_all_split

#print axioms FourCorner.IntegralModel.opposite_colour_residue_refinement
