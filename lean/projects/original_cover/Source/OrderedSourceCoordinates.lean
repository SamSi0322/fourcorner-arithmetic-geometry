import OrderedSourceRationalAlgebra
set_option linter.unusedSectionVars false
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open RationalAlgebra

def baseA : BaseField := RatFunc.X
def baseC : BaseField := RatFunc.C RatFunc.X
def baseN (n : ℚ) : BaseField := RatFunc.C (parameterN n)
def aCoord (n : ℚ) : sourceField n := algebraMap BaseField (sourceField n) baseA
def cCoord (n : ℚ) : sourceField n := algebraMap BaseField (sourceField n) baseC
def nCoord (n : ℚ) : sourceField n := algebraMap BaseField (sourceField n) (baseN n)
abbrev bCoord (n : ℚ) := orderedRoot n 0
abbrev ellCoord (n : ℚ) := orderedRoot n 1
abbrev uCoord (n : ℚ) := orderedRoot n 2
abbrev vCoord (n : ℚ) := orderedRoot n 3
abbrev hCoord (n : ℚ) := orderedRoot n 4

theorem nCoord_eq (n : ℚ) : nCoord n=algebraMap ℚ (sourceField n) n := by
  exact RingHom.congr_fun (Subsingleton.elim
    ((algebraMap BaseField (sourceField n)).comp
      ((RatFunc.C : CoefficientField →+* BaseField).comp (RatFunc.C : ℚ →+* CoefficientField)))
    (algebraMap ℚ (sourceField n))) n

theorem sourceValue_formula (n : ℚ) (i : Fin 5) : sourceValue n i=
    (![baseA*(baseA-baseN n)*(baseA+baseN n),baseC*(baseC-baseN n)*(baseC+baseN n),
       -(baseA*baseC)/baseN n,-((baseA-baseN n)*(baseC-baseN n))/baseN n,
       (baseA+baseC)/(2*(baseC+baseN n))] : Fin 5 → BaseField) i := by
  fin_cases i <;> simp [sourceValue,value,radicandPolynomial,baseA,baseC,baseN,
    map_add,map_sub,map_mul,map_div₀,RatFunc.algebraMap_X,RatFunc.algebraMap_C,
    RatFunc.algebraMap_eq_C, map_ofNat] <;> ring_nf <;> simp only [← add_mul, mul_inv_rev] <;> ring

theorem coordinate_squares (n : ℚ) (i : Fin 5) : (orderedRoot n i)^2=
    (![aCoord n*(aCoord n-nCoord n)*(aCoord n+nCoord n),
       cCoord n*(cCoord n-nCoord n)*(cCoord n+nCoord n),
       -(aCoord n*cCoord n)/nCoord n,-((aCoord n-nCoord n)*(cCoord n-nCoord n))/nCoord n,
       (aCoord n+cCoord n)/(2*(cCoord n+nCoord n))] : Fin 5 → sourceField n) i := by
  rw [orderedRoot_square,sourceValue_formula]
  fin_cases i <;> simp [aCoord,cCoord,nCoord,map_add,map_sub,map_mul,map_div₀,map_ofNat]

theorem outer_linear_ne_zero (z : CoefficientField) : (RatFunc.X : BaseField)-RatFunc.C z≠0 := by
  have hp : (Polynomial.X-Polynomial.C z : Polynomial CoefficientField)≠0 := by
    intro he
    have hh := congrArg (fun p : Polynomial CoefficientField => p.coeff 1) he
    norm_num [Polynomial.coeff_X] at hh
  have hh := OriginalRadicands.generic_polynomial_ne_zero
    (Polynomial.X-Polynomial.C z : Polynomial CoefficientField) hp
  simpa only [Polynomial.aeval_sub,Polynomial.aeval_X,Polynomial.aeval_C,RatFunc.algebraMap_eq_C] using hh

theorem n_ne (n : ℚ) (hn : n≠0) : nCoord n≠0 := by
  rw [nCoord_eq]
  exact (_root_.map_ne_zero (algebraMap ℚ (sourceField n))).mpr hn

theorem a_ne (n : ℚ) : aCoord n≠0 :=
 (_root_.map_ne_zero (algebraMap BaseField (sourceField n))).mpr RatFunc.X_ne_zero

theorem a_minus_ne (n : ℚ) : aCoord n-nCoord n≠0 := by
  simpa only [aCoord,nCoord,baseA,baseN,←map_sub] using
    (_root_.map_ne_zero (algebraMap BaseField (sourceField n))).mpr (outer_linear_ne_zero (parameterN n))
theorem a_plus_ne (n : ℚ) : aCoord n+nCoord n≠0 := by
  have hh := outer_linear_ne_zero (-parameterN n)
  simp only [map_neg,sub_neg_eq_add] at hh
  simpa only [aCoord,nCoord,baseA,baseN,←map_add] using
    (_root_.map_ne_zero (algebraMap BaseField (sourceField n))).mpr hh

def coefficientMap (n : ℚ) : CoefficientField →+* sourceField n :=
 (algebraMap BaseField (sourceField n)).comp RatFunc.C

theorem c_ne (n : ℚ) : cCoord n≠0 :=
 (_root_.map_ne_zero (coefficientMap n)).mpr RatFunc.X_ne_zero

theorem c_minus_ne (n : ℚ) (hn : n≠0) : cCoord n-nCoord n≠0 := by
  have hh := (_root_.map_ne_zero (coefficientMap n)).mpr (generic_parameter n hn).c_minus_ne
  simpa only [map_sub,coefficientMap,RingHom.comp_apply,cCoord,nCoord,baseC,baseN] using hh

theorem c_plus_ne (n : ℚ) (hn : n≠0) : cCoord n+nCoord n≠0 := by
  have hh := (_root_.map_ne_zero (coefficientMap n)).mpr (generic_parameter n hn).c_plus_ne
  simpa only [map_add,coefficientMap,RingHom.comp_apply,cCoord,nCoord,baseC,baseN] using hh

theorem a_c_ne (n : ℚ) : aCoord n+cCoord n≠0 := by
  have hh := outer_linear_ne_zero (-RatFunc.X)
  simp only [map_neg,sub_neg_eq_add] at hh
  simpa only [aCoord,cCoord,baseA,baseC,←map_add] using
    (_root_.map_ne_zero (algebraMap BaseField (sourceField n))).mpr hh

theorem b_ne (n : ℚ) : bCoord n≠0 := by
  intro he
  have hh := coordinate_squares n 0
  have hne := mul_ne_zero (mul_ne_zero (a_ne n) (a_minus_ne n)) (a_plus_ne n)
  apply hne
  simpa [bCoord,he] using hh.symm

theorem ell_ne_coord (n : ℚ) (hn : n≠0) : ellCoord n≠0 := by
  intro he
  have hh := coordinate_squares n 1
  have hne := mul_ne_zero (mul_ne_zero (c_ne n) (c_minus_ne n hn)) (c_plus_ne n hn)
  apply hne
  simpa [ellCoord,he] using hh.symm

theorem u_ne (n : ℚ) (hn : n≠0) : uCoord n≠0 := by
  intro he
  have hh := coordinate_squares n 2
  apply div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (a_ne n) (c_ne n))) (n_ne n hn)
  simpa [uCoord,he] using hh.symm

theorem v_ne (n : ℚ) (hn : n≠0) : vCoord n≠0 := by
  intro he
  have hh := coordinate_squares n 3
  apply div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (a_minus_ne n) (c_minus_ne n hn))) (n_ne n hn)
  simpa [vCoord,he] using hh.symm

theorem h_ne (n : ℚ) (hn : n≠0) : hCoord n≠0 := by
  intro he
  have hh := coordinate_squares n 4
  apply div_ne_zero (a_c_ne n) (mul_ne_zero (by norm_num : (2:sourceField n)≠0) (c_plus_ne n hn))
  simpa [hCoord,he] using hh.symm

def pureP (n : ℚ) := pairP (nCoord n) (aCoord n)
def pureBeta (n : ℚ) := pairBeta (nCoord n) (cCoord n)
def pureU (n : ℚ) := pairU (nCoord n) (aCoord n) (bCoord n) (ellCoord n) (uCoord n) (vCoord n)
def pureV (n : ℚ) := pairV (aCoord n) (bCoord n) (vCoord n)
def pureW (n : ℚ) := pairW (nCoord n) (aCoord n) (uCoord n) (vCoord n)
def pureT (n : ℚ) := pairT (nCoord n) (aCoord n) (bCoord n) (ellCoord n) (uCoord n) (vCoord n) (hCoord n)

theorem pureU_square (n : ℚ) (hn : n≠0) : pureU n^2=pureP n*pureBeta n := by
  apply pairU_square (a_ne n) (a_minus_ne n) (a_plus_ne n) (c_minus_ne n hn) (n_ne n hn)
    (coordinate_squares n 0) (coordinate_squares n 3)
  exact ordinateW_square (n_ne n hn) (a_ne n) (c_ne n) (a_minus_ne n) (c_minus_ne n hn)
    (coordinate_squares n 0) (coordinate_squares n 1) (coordinate_squares n 2) (coordinate_squares n 3)
theorem pureV_square (n : ℚ) (hn : n≠0) : pureV n^2=2*(pureP n-1)*(pureBeta n-1) :=
 pairV_square (a_ne n) (a_minus_ne n) (c_minus_ne n hn) (n_ne n hn)
    (coordinate_squares n 0) (coordinate_squares n 3)
theorem pureW_square (n : ℚ) (hn : n≠0) : pureW n^2=2*(pureP n+1)*(pureBeta n+1) :=
 pairW_square (a_ne n) (a_minus_ne n) (c_minus_ne n hn) (n_ne n hn)
    (coordinate_squares n 2) (coordinate_squares n 3)
theorem pureT_square (n : ℚ) (hn : n≠0) : pureT n^2=(pureP n-1)*pureBeta n+pureP n+1 :=
 pairT_square (a_ne n) (c_minus_ne n hn) (c_plus_ne n hn) (pureU_square n hn) (coordinate_squares n 4)

theorem pureU_ne (n : ℚ) (hn : n≠0) : pureU n≠0 := by
  have hh := pairU_simplified (ℓ:=ellCoord n) (n_ne n hn) (b_ne n) (u_ne n hn) (v_ne n hn)
    (c_minus_ne n hn) (coordinate_squares n 3)
  change pureU n=_ at hh
  rw [hh]
  exact div_ne_zero (ell_ne_coord n hn) (mul_ne_zero (u_ne n hn) (c_minus_ne n hn))
theorem pureT_ne (n : ℚ) (hn : n≠0) : pureT n≠0 :=
 mul_ne_zero (mul_ne_zero (by norm_num) (pureU_ne n hn)) (h_ne n hn)

/-- The source's actual image in the six ordered original coordinates. -/
def originalImage (n : ℚ) : Fin 6 → sourceField n := pureReturn (pureU n) (pureV n) (pureW n) (pureT n)
theorem originalImage_relations (n : ℚ) (hn : n≠0) : ∀i,originalRelations (originalImage n) i=0 :=
 pureReturn_relations _ _ _ _ _ _ (pureT_ne n hn) (pureU_square n hn) (pureV_square n hn)
   (pureW_square n hn) (pureT_square n hn)

def originalCoordinateMap (n : ℚ) (hn : n≠0) : OriginalRing →ₐ[ℚ] sourceField n :=
 originalLift (originalImage n) (originalImage_relations n hn)

#print axioms originalImage_relations
#print axioms originalCoordinateMap
end FourCorner.OriginalCoverCompletion.OrderedSource
