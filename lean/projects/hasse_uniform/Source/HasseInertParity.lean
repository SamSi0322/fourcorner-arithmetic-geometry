import HasseTwoSymbol

namespace FourCorner.HasseInertParity

open HilbertArithmeticHigh11 HasseObstructionArithmetic HasseParameterSupport
open HasseRationalSource HasseAnchorChoice HasseInertSupport HasseSignAlgebra

theorem prime_of_rationalSupport (r : ℚ) (q : ℕ) (h : q∈rationalSupport r) : q.Prime := by
  rcases Finset.mem_union.mp h with h | h
  · exact Nat.prime_of_mem_primeFactors h
  · exact Nat.prime_of_mem_primeFactors h

theorem prime_of_parameterSupport (p : ℚ) (q : ℕ) (hq0 : q ≠ 0) (hq2 : q ≠ 2)
    (h : q∈parameterSupport p) : q.Prime := by
  simp only [parameterSupport,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with ((h | h) | h) | h
  · exact False.elim (h.elim hq0 hq2)
  · exact prime_of_rationalSupport p q h
  · exact prime_of_rationalSupport (p-1) q h
  · exact prime_of_rationalSupport (p+1) q h

theorem oddParameterSupport_prime (p : ℚ) (q : ℕ) (h : q∈oddParameterSupport p) : q.Prime ∧ q ≠ 2 := by
  have hh : q ≠ 2 ∧ q ≠ 0 ∧ q∈parameterSupport p := by simpa only [oddParameterSupport,Finset.mem_erase] using h
  exact ⟨prime_of_parameterSupport p q hh.2.1 hh.1 hh.2.2,hh.1⟩

theorem val_two (q : OddPrime) : padicValRat q.val (2 : ℚ)=0 := by
  have hd : ¬ q.val ∣ 2 := fun hd => q.property.2
    ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
  simpa only [Nat.cast_ofNat,padicValNat.eq_zero_of_not_dvd hd,Nat.cast_zero] using
    (padicValRat.of_nat (p:=q.val) (n:=2))

theorem negative_a_equal_b (q : OddPrime) (p : ℚ) (hp : 1<p)
    (h : padicValRat q.val (p-1)<0) : padicValRat q.val (p+1)=padicValRat q.val (p-1) := by
  have he : p-1+2=p+1 := by ring
  have hh := padicValRat.add_eq_of_lt (p:=q.val) (q:=p-1) (r:=2)
    (by rw [he]; linarith) (by linarith) (by norm_num) (by rw [val_two q]; exact h)
  simpa only [he] using hh

theorem positive_a_b_zero (q : OddPrime) (p : ℚ) (hp : 1<p)
    (h : 0<padicValRat q.val (p-1)) : padicValRat q.val (p+1)=0 := by
  have he : 2+(p-1)=p+1 := by ring
  have hh := padicValRat.add_eq_of_lt (p:=q.val) (q:=2) (r:=p-1)
    (by rw [he]; linarith) (by norm_num) (by linarith) (by rw [val_two q]; exact h)
  simpa only [he,val_two q] using hh

theorem negative_b_equal_a (q : OddPrime) (p : ℚ) (hp : 1<p)
    (h : padicValRat q.val (p+1)<0) : padicValRat q.val (p-1)=padicValRat q.val (p+1) := by
  have he : p+1+(-2)=p-1 := by ring
  have htwo : padicValRat q.val (-2 : ℚ)=0 := by rw [padicValRat.neg,val_two q]
  have hh := padicValRat.add_eq_of_lt (p:=q.val) (q:=p+1) (r:=-2)
    (by rw [he]; linarith) (by linarith) (by norm_num) (by rw [htwo]; exact h)
  simpa only [he] using hh

def positiveHalf (v : ℤ) : ZMod 2 := if 0<v then (v/2 : ℤ) else 0

/-- The literal w/z parity equals exactly the two positive half-valuation
terms; negative neighbor valuations cancel, rather than being dropped. -/
theorem source_support_bit (q : OddPrime) (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) (h2 : ¬ IsSquare (2 : ZMod q.val)) :
    (padicValRat q.val (D.w/P.Z) : ZMod 2)=
      positiveHalf (padicValRat q.val (p-1))+positiveHalf (padicValRat q.val (p+1)) := by
  have hs := (source_support q p hp P D (SqrtTwoGlobalNorm.nonsquare_two_completion h2)).2
  obtain ⟨ha,hb⟩ := half_valuations_integral p hp hL q.val q.property.2 h2
  rcases lt_trichotomy (padicValRat q.val (p-1)) 0 with hn | hz | hpos
  · have he := negative_a_equal_b q p hp hn
    rw [he] at hs
    have hv : padicValRat q.val (D.w/P.Z)=0 := by omega
    rw [hv,he]
    simp only [positiveHalf,not_lt_of_ge (le_of_lt hn),ite_false,Int.cast_zero,add_zero]
  · have hbn : 0≤padicValRat q.val (p+1) := by
      by_contra hbn
      have he := negative_b_equal_a q p hp (by omega)
      rw [hz] at he
      omega
    have hv : padicValRat q.val (D.w/P.Z)=padicValRat q.val (p+1)/2 := by omega
    rw [hv,hz]
    by_cases hbpos : 0<padicValRat q.val (p+1)
    · simp only [positiveHalf,lt_self_iff_false,ite_false,zero_add,if_pos hbpos]
    · have hbzero : padicValRat q.val (p+1)=0 := by omega
      simp [positiveHalf,hbzero]
  · have he := positive_a_b_zero q p hp hpos
    have hv : padicValRat q.val (D.w/P.Z)= -(padicValRat q.val (p-1)/2) := by omega
    rw [hv,he]
    simp only [positiveHalf,if_pos hpos,lt_self_iff_false,ite_false,add_zero,Int.cast_neg]
    exact (by decide : ∀ x : ZMod 2, -x=x) _

#print axioms source_support_bit

end FourCorner.HasseInertParity
