import OriginalQuadraticDegree
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

/-- A simple finite zero prevents a polynomial from being square in K(a). -/
theorem not_isSquare_of_simple_zero (p : K[X]) (z : K)
    (hp : p.eval z=0) (hd : p.derivative.eval z ≠ 0) :
    ¬IsSquare (algebraMap K[X] (RatFunc K) p) := by
  intro hs
  obtain ⟨q,hq⟩ := (FourCorner.CoverFields.isSquare_algebraMap_iff (F:=RatFunc K) p).mp hs
  have hz : q.eval z=0 := by
    have he := congrArg (fun p : K[X] => p.eval z) hq
    simp only [eval_mul,hp] at he
    exact mul_self_eq_zero.mp he.symm
  apply hd
  rw [hq,derivative_mul,eval_add,eval_mul,eval_mul,hz]
  ring

theorem product_not_isSquare_of_unique_simple_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → K[X]) (i : ι) (hi : i∈s) (z : K)
    (hf : (f i).eval z=0) (hd : (f i).derivative.eval z≠0)
    (hothers : ∀ j∈s, j≠i → (f j).eval z≠0) :
    ¬IsSquare (algebraMap K[X] (RatFunc K) (∏ j∈s,f j)) := by
  have hfac : (∏ j∈s,f j)=f i*(∏ j∈s.erase i,f j) := (Finset.mul_prod_erase s f hi).symm
  apply not_isSquare_of_simple_zero _ z
  · rw [hfac,eval_mul,hf,zero_mul]
  · rw [hfac,derivative_mul,eval_add,eval_mul,eval_mul,hf,zero_mul,add_zero]
    apply mul_ne_zero hd
    rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      exact hothers j hj'.2 hj'.1)

/-- The literal b², ell², u², v², h². This presentation is independent of S. -/
def radicandPolynomial (n c : K) : Fin 5 → K[X]
 | 0 => X*(X-C n)*(X+C n)
 | 1 => C (c*(c-n)*(c+n))
 | 2 => C (-c/n)*X
 | 3 => C (-(c-n)/n)*(X-C n)
 | 4 => C (1/(2*(c+n)))*(X+C c)
def value (n c : K) (i : Fin 5) : RatFunc K :=
 algebraMap K[X] (RatFunc K) (radicandPolynomial n c i)
structure GenericParameter (n c : K) : Prop where
 n_ne : n≠0
 c_ne : c≠0
 c_minus_ne : c-n≠0
 c_plus_ne : c+n≠0
 ell_nonsquare : ¬IsSquare (c*(c-n)*(c+n))
private theorem ell_ne (n c : K) (h : GenericParameter n c) : c*(c-n)*(c+n)≠0 :=
 mul_ne_zero (mul_ne_zero h.c_ne h.c_minus_ne) h.c_plus_ne

private theorem eval_minus_n_ne (n c : K) (h : GenericParameter n c) (i : Fin 5) (hi : i≠0) :
 (radicandPolynomial n c i).eval (-n)≠0 := by
  fin_cases i
  · exact (hi rfl).elim
  · simpa [radicandPolynomial] using ell_ne n c h
  · have he : (-c/n)*(-n)=c := by field_simp [h.n_ne]
    simpa only [radicandPolynomial,eval_mul,eval_C,eval_X,he] using h.c_ne
  · have he : (-(c-n)/n)*(-n-n)=2*(c-n) := by field_simp [h.n_ne]; ring
    simpa only [radicandPolynomial,eval_mul,eval_C,eval_sub,eval_X,he] using
      mul_ne_zero (by norm_num : (2:K)≠0) h.c_minus_ne
  · have he : (radicandPolynomial n c 4).eval (-n)=(c-n)/(2*(c+n)) := by
      simp only [radicandPolynomial,eval_mul,eval_C,eval_add,eval_X]; ring
    change (radicandPolynomial n c (4:Fin 5)).eval (-n)≠0
    rw [he]
    exact div_ne_zero h.c_minus_ne (mul_ne_zero (by norm_num : (2:K)≠0) h.c_plus_ne)

private theorem eval_minus_c_ne (n c : K) (h : GenericParameter n c) (i : Fin 5) (hi : i≠4) :
 (radicandPolynomial n c i).eval (-c)≠0 := by
  fin_cases i
  · have he : (radicandPolynomial n c 0).eval (-c)=-(c*(c-n)*(c+n)) := by
      simp only [radicandPolynomial,eval_mul,eval_sub,eval_add,eval_X,eval_C]; ring
    change (radicandPolynomial n c (0:Fin 5)).eval (-c)≠0
    rw [he]
    exact neg_ne_zero.mpr (ell_ne n c h)
  · simpa [radicandPolynomial] using ell_ne n c h
  · have he : (-c/n)*(-c)=c^2/n := by ring
    simpa only [radicandPolynomial,eval_mul,eval_C,eval_X,he] using
      div_ne_zero (pow_ne_zero 2 h.c_ne) h.n_ne
  · have he : (-(c-n)/n)*(-c-n)=(c-n)*(c+n)/n := by ring
    simpa only [radicandPolynomial,eval_mul,eval_C,eval_sub,eval_X,he] using
      div_ne_zero (mul_ne_zero h.c_minus_ne h.c_plus_ne) h.n_ne
  · exact (hi rfl).elim

theorem independent_products (n c : K) (h : GenericParameter n c)
    (s : Finset (Fin 5)) (hs : s.Nonempty) : ¬IsSquare (∏ i∈s,value n c i) := by
  simp only [value]
  rw [← map_prod]
  by_cases h0 : 0∈s
  · apply product_not_isSquare_of_unique_simple_zero s (radicandPolynomial n c) 0 h0 (-n)
    · simp [radicandPolynomial]
    · have he : ((radicandPolynomial n c 0).derivative).eval (-n)=2*n^2 := by
        simp [radicandPolynomial,derivative_mul]; ring
      rw [he]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 h.n_ne)
    · exact fun j hj hji => eval_minus_n_ne n c h j hji
  by_cases h4 : 4∈s
  · apply product_not_isSquare_of_unique_simple_zero s (radicandPolynomial n c) 4 h4 (-c)
    · simp [radicandPolynomial]
    · simpa [radicandPolynomial,derivative_mul] using
        one_div_ne_zero (mul_ne_zero (by norm_num : (2:K)≠0) h.c_plus_ne)
    · exact fun j hj hji => eval_minus_c_ne n c h j hji
  by_cases h2 : 2∈s
  · apply product_not_isSquare_of_unique_simple_zero s (radicandPolynomial n c) 2 h2 0
    · simp [radicandPolynomial]
    · simpa [radicandPolynomial,derivative_mul] using div_ne_zero (neg_ne_zero.mpr h.c_ne) h.n_ne
    · intro j hj hji
      fin_cases j
      · exact (h0 hj).elim
      · simpa [radicandPolynomial] using ell_ne n c h
      · exact (hji rfl).elim
      · have he : (-(c-n)/n)*(-n)=c-n := by field_simp [h.n_ne]
        simpa only [radicandPolynomial,eval_mul,eval_C,eval_sub,eval_X,zero_sub,he] using h.c_minus_ne
      · exact (h4 hj).elim
  by_cases h3 : 3∈s
  · apply product_not_isSquare_of_unique_simple_zero s (radicandPolynomial n c) 3 h3 n
    · simp [radicandPolynomial]
    · simpa [radicandPolynomial,derivative_mul] using div_ne_zero (neg_ne_zero.mpr h.c_minus_ne) h.n_ne
    · intro j hj hji
      fin_cases j
      · exact (h0 hj).elim
      · simpa [radicandPolynomial] using ell_ne n c h
      · exact (h2 hj).elim
      · exact (hji rfl).elim
      · exact (h4 hj).elim
  have he : s={1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    obtain ⟨i,hi⟩ := hs
    have hall : ∀j∈s,j=1 := by
      intro j hj; fin_cases j
      · exact (h0 hj).elim
      · rfl
      · exact (h2 hj).elim
      · exact (h3 hj).elim
      · exact (h4 hj).elim
    exact ⟨hall i hi ▸ hi,hall⟩
  rw [he]
  simpa [radicandPolynomial] using constant_nonsquare_ratFunc _ h.ell_nonsquare

abbrev CoefficientField := RatFunc ℚ
abbrev BaseField := RatFunc CoefficientField
def parameterN (n : ℚ) : CoefficientField := RatFunc.C n
def sourceValue (n : ℚ) : Fin 5 → BaseField := value (parameterN n) RatFunc.X

theorem generic_parameter (n : ℚ) (hn : n≠0) : GenericParameter (parameterN n) (RatFunc.X : CoefficientField) := by
  constructor
  · exact (_root_.map_ne_zero (RatFunc.C : ℚ →+* CoefficientField)).mpr hn
  · exact RatFunc.X_ne_zero
  · have hp : (X-C n : ℚ[X])≠0 := by
      intro hp; have hh := congrArg (fun p : ℚ[X] => p.coeff 1) hp; norm_num [coeff_X] at hh
    have hh := OriginalRadicands.generic_polynomial_ne_zero (X-C n : ℚ[X]) hp
    simpa only [aeval_sub,aeval_X,aeval_C,parameterN,RatFunc.algebraMap_eq_C] using hh
  · have hp : (X+C n : ℚ[X])≠0 := by
      intro hp; have hh := congrArg (fun p : ℚ[X] => p.coeff 1) hp; norm_num [coeff_X] at hh
    have hh := OriginalRadicands.generic_polynomial_ne_zero (X+C n : ℚ[X]) hp
    simpa only [aeval_add,aeval_X,aeval_C,parameterN,RatFunc.algebraMap_eq_C] using hh
  · have hh : ¬IsSquare (algebraMap ℚ[X] CoefficientField (X*(X-C n)*(X+C n))) := by
      apply not_isSquare_of_simple_zero _ 0
      · simp
      · have he : (X*(X-C n)*(X+C n) : ℚ[X]).derivative.eval 0= -(n^2) := by simp; ring
        rw [he]
        exact neg_ne_zero.mpr (pow_ne_zero 2 hn)
    simpa only [map_mul,map_sub,map_add,RatFunc.algebraMap_X,RatFunc.algebraMap_C,
      parameterN,RatFunc.algebraMap_eq_C] using hh

theorem source_products_nonsquare (n : ℚ) (hn : n≠0) (s : Finset (Fin 5)) (hs : s.Nonempty) :
    ¬IsSquare (∏ i∈s,sourceValue n i) := independent_products _ _ (generic_parameter n hn) s hs

#print axioms source_products_nonsquare
end FourCorner.OriginalCoverCompletion.OrderedSource
