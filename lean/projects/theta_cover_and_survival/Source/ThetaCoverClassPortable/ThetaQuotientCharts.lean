import ThetaCoverClassPortable.ThetaOriginImage
import ThetaCoverClassPortable.ThetaPolynomialFunext
noncomputable section
namespace FourCorner.ThetaQuotientCharts
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

def sourceIndex (j : Fin 3) : Fin 5 := j.castSucc.castSucc
def targetIndex : Fin 3 → Fin 3
  | 0=>2 | 1=>0 | 2=>1
abbrev RA := MvPolynomial (Fin 2) ℚ
abbrev SA := MvPolynomial (Fin 4) ℚ
abbrev re (j : Fin 3) := ThetaQuotientChart.affineEquation (targetEquation ℚ) (targetIndex j) 0
abbrev se (j : Fin 3) (a : Fin 3) := ThetaQuotientChart.affineEquation (sourceEquation ℚ) (sourceIndex j) a
abbrev R (j : Fin 3) := ThetaProjectiveModel.affineRing (targetEquation ℚ) (targetIndex j)
abbrev S (j : Fin 3) := ThetaProjectiveModel.affineRing (sourceEquation ℚ) (sourceIndex j)
instance (j : Fin 3) : Algebra ℚ (R j) := Ideal.Quotient.algebra ℚ
instance (j : Fin 3) : Algebra ℚ (S j) := Ideal.Quotient.algebra ℚ
def rq (j : Fin 3) : RA →ₐ[ℚ] R j := Ideal.Quotient.mkₐ _ _
def smk (j : Fin 3) : SA →ₐ[ℚ] S j := Ideal.Quotient.mkₐ _ _
def rcoords (j a : Fin 3) : RA :=
  match j,a with
  | 0,0=>1 | 0,1=>X 0 | 0,2=>X 1
  | 1,0=>X 1 | 1,1=>1 | 1,2=>X 0
  | 2,0=>X 1 | 2,1=>X 0 | 2,2=>1
def scoords (j a : Fin 3) : SA :=
  match j,a with
  | 0,0=>1 | 0,1=>X 0 | 0,2=>X 1
  | 1,0=>X 0 | 1,1=>1 | 1,2=>X 1
  | 2,0=>X 0 | 2,1=>X 1 | 2,2=>1
def basePolys (j : Fin 3) (a : Fin 2) : SA :=
  match j,a with
  | 0,0=>X 0 | 0,1=>X 1
  | 1,0=>X 1 | 1,1=>X 0
  | 2,0=>X 1 | 2,1=>X 0
def subst (j : Fin 3) : RA →ₐ[ℚ] SA := aeval (basePolys j)
def shift : Fin 3 → ℚ | 0=>0 | 1=>7 | 2=> -7
def lambda : Fin 3 → ℚ | 0=>50 | 1=>2 | 2=>2

def bpoly (j : Fin 3) : RA := C (1/2)*(rcoords j 1^2+rcoords j 2^2-2*rcoords j 0^2)
def cpoly (j : Fin 3) : RA := C (1/28)*(rcoords j 1^2-rcoords j 2^2)+C (shift j)*bpoly j
def apoly (j : Fin 3) : RA := 1-C (lambda j)*bpoly j
def upoly (j : Fin 3) : SA := X 2+C (shift j)*X 3
def seFormula (j : Fin 3) : Fin 3 → SA
  | 0=>scoords j 0^2-X 2^2-50*X 3^2
  | 1=>scoords j 1^2-X 2^2-14*X 2*X 3-51*X 3^2
  | 2=>scoords j 2^2-X 2^2+14*X 2*X 3-51*X 3^2
lemma source_equation_formula (j a : Fin 3) : se j a=seFormula j a := by
  fin_cases j <;> fin_cases a
  all_goals simp [se,sourceIndex,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    sourceEquation,ThetaActualPoints.source_drop,scoords,seFormula,map_ofNat]
  all_goals ring
lemma target_equation_formula (j : Fin 3) : re j=
    9801*(rcoords j 1^4+rcoords j 2^4)+19598*rcoords j 1^2*rcoords j 2^2-
      39592*(rcoords j 1^2+rcoords j 2^2)*rcoords j 0^2+39984*rcoords j 0^4 := by
  fin_cases j
  all_goals simp [re,targetIndex,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,rcoords,map_ofNat]
  all_goals ring
lemma conic_identity (j : Fin 3) : apoly j*bpoly j-cpoly j^2=C (-1/784)*re j := by
  rw [target_equation_formula]
  fin_cases j
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals norm_num [apoly,bpoly,cpoly,rcoords,shift,lambda,map_ofNat]
  all_goals ring
lemma source_b_identity (j : Fin 3) : X 3^2-subst j (bpoly j)=se j 0-C (1/2)*(se j 1+se j 2) := by
  simp only [source_equation_formula]
  fin_cases j
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals norm_num [subst,aeval_def,basePolys,bpoly,rcoords,scoords,seFormula,map_ofNat]
  all_goals ring
lemma source_c_identity (j : Fin 3) : upoly j*X 3-subst j (cpoly j)=
    -C (1/28)*(se j 1-se j 2)+C (shift j)*(X 3^2-subst j (bpoly j)) := by
  simp only [source_equation_formula]
  fin_cases j
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals norm_num [subst,aeval_def,basePolys,bpoly,cpoly,upoly,rcoords,scoords,seFormula,shift,map_ofNat]
  all_goals ring
lemma source_a_identity (j : Fin 3) : upoly j^2-subst j (apoly j)=
    -se j j-C (lambda j)*(X 3^2-subst j (bpoly j)) := by
  rw [source_equation_formula]
  fin_cases j
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals norm_num [subst,aeval_def,basePolys,bpoly,apoly,upoly,rcoords,scoords,seFormula,shift,lambda,map_ofNat]
  all_goals ring
lemma rrelation (j : Fin 3) : rq j (re j)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
lemma srelation (j a : Fin 3) : smk j (se j a)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,rfl⟩)
def b (j : Fin 3) : R j := rq j (bpoly j)
def c (j : Fin 3) : R j := rq j (cpoly j)
def a (j : Fin 3) : R j := rq j (apoly j)
lemma base_conic (j : Fin 3) : a j*b j=c j^2 := by
  have h:=congrArg (rq j) (conic_identity j)
  simpa only [map_sub,map_mul,map_pow,rrelation,mul_zero,sub_eq_zero,a,b,c] using h
lemma base_unit_ideal (j : Fin 3) : a j+algebraMap ℚ (R j) (lambda j)*b j=1 := by
  change rq j (apoly j)+rq j (C (lambda j))*rq j (bpoly j)=1
  rw [←map_mul,←map_add]
  simp [apoly]
end FourCorner.ThetaQuotientCharts
#print axioms FourCorner.ThetaQuotientCharts.conic_identity
#print axioms FourCorner.ThetaQuotientCharts.source_b_identity
#print axioms FourCorner.ThetaQuotientCharts.source_c_identity
#print axioms FourCorner.ThetaQuotientCharts.source_a_identity
#print axioms FourCorner.ThetaQuotientCharts.base_conic
#print axioms FourCorner.ThetaQuotientCharts.base_unit_ideal
