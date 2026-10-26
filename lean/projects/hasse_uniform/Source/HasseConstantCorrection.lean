import HasseTwoSymbol

namespace FourCorner.HasseConstantCorrection

open HasseTangentGlobal HasseParameterSupport HasseObstructionArithmetic HasseHilbertArithmetic
open HasseRationalSource HasseAnchorChoice HilbertWellDefinedHigh11

noncomputable def constantSign (p : ℚ) (hp : 1<p) (v : ℕ) : ℤ :=
  rationalSign (firstCoefficient p) (-2) (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) v

theorem constantSign_sq_one (p : ℚ) (hp : 1<p) (v : ℕ) : (constantSign p hp v)^2=1 :=
  rationalSign_sq_one _ _ _ _ v

theorem constantSign_real (p : ℚ) (hp : 1<p) : constantSign p hp 0= -1 := by
  rw [constantSign,rationalSign_real]
  simp only [firstCoefficient_negative p hp,show (-2 : ℚ)<0 by norm_num,and_self,ite_true]

theorem constantSign_one_outside_parameter_support (p : ℚ) (hp : 1<p) (v : ℕ)
    (hv : v ∉ parameterSupport p) : constantSign p hp v=1 := by
  have hvs : v≠0 ∧ v≠2 ∧ v∉rationalSupport p ∧ v∉rationalSupport (p-1) ∧ v∉rationalSupport (p+1) := by
    simpa only [parameterSupport,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc] using hv
  by_cases hq : v.Prime
  · letI : Fact v.Prime := ⟨hq⟩
    apply rationalSign_one_of_even_valuations ⟨v,hq,hvs.2.1⟩
    · change Even (padicValRat v (-(p-1)))
      rw [padicValRat.neg,valuation_zero_outside_support (p-1) (by linarith) v hq hvs.2.2.2.1]
      exact ⟨0,by simp⟩
    · have htwo := commonRoot_val_two (p:=v) hvs.2.1
      change Even (padicValRat v (-2))
      rw [padicValRat.neg]
      have hh : padicValRat v (2 : ℚ)=0 := by
        have hd : ¬ v ∣ 2 := fun hd => hvs.2.1
          ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hq.ne_one)
        simpa only [Nat.cast_ofNat,padicValNat.eq_zero_of_not_dvd hd,Nat.cast_zero] using
          (padicValRat.of_nat (p:=v) (n:=2))
      rw [hh]
      exact ⟨0,by simp⟩
  · exact rationalSign_one_of_not_prime _ _ _ _ v hvs.1 hvs.2.1 hq

theorem constantSign_parameter_product (p : ℚ) (hp : 1<p) :
    (∏ v ∈ parameterSupport p,constantSign p hp v)=1 := by
  let S := {0,2} ∪ rationalSupport (firstCoefficient p) ∪ rationalSupport (-2)
  let T := parameterSupport p
  have hglob : (∏ v ∈ S,constantSign p hp v)=1 :=
    rational_reciprocity_on_rational_support _ _ _ _
  have hout : ∀ v, v∉S → constantSign p hp v=1 := by
    intro v hv
    exact rationalSign_one_outside_rational_support _ _ _ _ v hv
  have hleft : (∏ v ∈ S ∪ T,constantSign p hp v)=(∏ v ∈ S,constantSign p hp v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_left
    intro v hv hn
    exact hout v hn
  have hright : (∏ v ∈ S ∪ T,constantSign p hp v)=(∏ v ∈ T,constantSign p hp v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_right
    intro v hv hn
    exact constantSign_one_outside_parameter_support p hp v hn
  exact hright.symm.trans (hleft.trans hglob)

noncomputable def correctedSign (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) (v : ℕ) : ℤ := tangentSign p hp P D v*constantSign p hp v

theorem correctedSign_real (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P) :
    correctedSign p hp P D 0=1 := by
  rw [correctedSign,tangentSign_real,constantSign_real]
  norm_num

theorem correctedSign_parameter_product (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P) :
    (∏ v ∈ parameterSupport p,correctedSign p hp P D v)=1 := by
  simp only [correctedSign,Finset.prod_mul_distrib,tangentSign_parameter_product,
    constantSign_parameter_product,one_mul]

theorem correctedSign_parameter_finite_product (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    correctedSign p hp P D 2*(∏ q ∈ oddParameterSupport p,correctedSign p hp P D q)=1 := by
  have h0 : 0∈parameterSupport p := by simp [parameterSupport]
  have h2 : 2∈(parameterSupport p).erase 0 := by simp [parameterSupport]
  have he := Finset.mul_prod_erase (parameterSupport p) (correctedSign p hp P D) h0
  have he2 := Finset.mul_prod_erase ((parameterSupport p).erase 0) (correctedSign p hp P D) h2
  rw [correctedSign_real,one_mul,correctedSign_parameter_product] at he
  exact he2.trans he

#print axioms constantSign_real
#print axioms constantSign_parameter_product
#print axioms correctedSign_parameter_product
#print axioms correctedSign_parameter_finite_product

end FourCorner.HasseConstantCorrection
