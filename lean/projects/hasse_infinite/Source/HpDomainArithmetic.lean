import HasseUniformNoPoint
import FourCorner.SquareArea

namespace FourCorner.HpDomainArithmetic

/-- A genuine rational right triangle of area one would result if this
positive congruent-number radicand were a rational square. -/
theorem pab_not_square (p : ℚ) (hp : 1<p) : ¬ IsSquare (p*(p^2-1)) := by
  rintro ⟨y,hy⟩
  have hy2 : y^2=p*(p^2-1) := by simpa only [pow_two] using hy.symm
  have hp0 : 0<p := by linarith
  have hpa : 0<p^2-1 := by nlinarith
  have hy0 : y ≠ 0 := by intro h;rw [h] at hy2;nlinarith
  let d := |y|
  have hd : 0<d := abs_pos.mpr hy0
  have hd2 : d^2=p*(p^2-1) := by simpa only [d,sq_abs] using hy2
  have htri : ((p^2-1)/d)^2+(2*p/d)^2=((p^2+1)/d)^2 := by
    field_simp
    ring
  have harea : ((p^2-1)/d)*(2*p/d)/2=(1 : ℚ)^2 := by
    field_simp
    linear_combination -hd2
  exact rational_right_triangle_not_square_area (div_pos hpa hd) (div_pos (by positivity) hd)
    (by norm_num : (0 : ℚ)<1) htri harea

/-- The paper domain follows from the exact dyadic parity and Fermat's
square-area theorem, with a genuine positive squarefree rational kernel. -/
theorem domain_of_even_dyadic (p : ℚ) (hp : 1<p)
    (he : Even (padicValRat 2 (p*(p^2-1)))) : HasseNorms.Domain p := by
  have hprod : 0<p*(p^2-1) := mul_pos (by linarith) (by nlinarith)
  obtain ⟨n,hn,hnSF,k,hk,hEq⟩ := positive_rat_squarefree_decomposition hprod
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hn1 : n ≠ 1 := by
    intro h
    apply pab_not_square p hp
    refine ⟨k,?_⟩
    simpa only [h,Nat.cast_one,one_mul,pow_two] using hEq
  have hnen : Even (padicValRat 2 (n : ℚ)) := by
    have hv := congrArg (padicValRat 2) hEq
    rw [padicValRat.mul hnq (pow_ne_zero _ hk0),padicValRat.pow] at hv
    rw [Int.even_iff] at he ⊢
    norm_num only [Nat.cast_ofNat] at hv
    omega
  have hvnat : padicValRat 2 (n : ℚ)=(padicValNat 2 n : ℤ) := padicValRat.of_nat
  have hvfac : n.factorization 2=padicValNat 2 n := n.factorization_def Nat.prime_two
  have hvle : padicValNat 2 n≤1 := by rw [← hvfac];exact hnSF.natFactorization_le_one 2
  have hvzero : padicValNat 2 n=0 := by
    rw [hvnat,Int.even_iff] at hnen
    omega
  have hnOdd : Odd n := by
    apply Nat.not_even_iff_odd.mp
    intro hEven
    have hdiv : 2∣n := even_iff_two_dvd.mp hEven
    have hh := one_le_padicValNat_of_dvd hn0 hdiv
    rw [hvzero] at hh
    omega
  exact ⟨n,by omega,hnOdd,hnSF,k,hk0,hEq⟩

#print axioms pab_not_square
#print axioms domain_of_even_dyadic

end FourCorner.HpDomainArithmetic
