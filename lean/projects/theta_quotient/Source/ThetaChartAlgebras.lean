import ThetaQuotientCharts
noncomputable section
namespace FourCorner.ThetaChartAlgebras
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaQuotientCharts
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

def coefficient0 (j : Fin 3) : SA :=
  39984*scoords j 0^2+39984*X 2^2+1999200*X 3^2-39592*(scoords j 1^2+scoords j 2^2)
def coefficient1 (j : Fin 3) : SA :=
  9801*scoords j 1^2+9801*(X 2^2+14*X 2*X 3+51*X 3^2)+19598*scoords j 2^2-
    39592*(X 2^2+50*X 3^2)
def coefficient2 (j : Fin 3) : SA :=
  9801*scoords j 2^2+9801*(X 2^2-14*X 2*X 3+51*X 3^2)+
    19598*(X 2^2+14*X 2*X 3+51*X 3^2)-39592*(X 2^2+50*X 3^2)
lemma target_pullback_identity (j : Fin 3) : subst j (re j)=
    coefficient0 j*se j 0+coefficient1 j*se j 1+coefficient2 j*se j 2 := by
  simp only [target_equation_formula,source_equation_formula]
  fin_cases j
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals norm_num [subst,aeval_def,basePolys,rcoords,scoords,seFormula,
    coefficient0,coefficient1,coefficient2,map_ofNat]
  all_goals ring
lemma target_vanishes (j : Fin 3) : smk j (subst j (re j))=0 := by
  rw [target_pullback_identity]
  simp only [map_add,map_mul,srelation,mul_zero,add_zero]
/-- Actual map between the literal target and source dehomogenized coordinate algebras,
for all three P/Q/R projection charts. -/
def baseMap (j : Fin 3) : R j →ₐ[ℚ] S j :=
  Ideal.Quotient.liftₐ _ ((smk j).comp (subst j)) (by
    have hh : ThetaQuotientChart.affineIdeal (ThetaLiteralModels.targetEquation ℚ) (targetIndex j)≤
        RingHom.ker ((smk j).comp (subst j)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact target_vanishes j
    exact fun x hx=>hh hx)
@[simp] lemma baseMap_rq (j : Fin 3) (p : RA) : baseMap j (rq j p)=smk j (subst j p) := rfl
instance sourceAlgebra (j : Fin 3) : Algebra (R j) (S j) := (baseMap j).toRingHom.toAlgebra
instance sourceScalarTower (j : Fin 3) : IsScalarTower ℚ (R j) (S j) where
  smul_assoc q r s := by
    change baseMap j (q • r)*s=q • (baseMap j r*s)
    rw [map_smul]
    exact smul_mul_assoc q (baseMap j r) s
lemma algebraMap_eq_baseMap (j : Fin 3) : algebraMap (R j) (S j)=(baseMap j).toRingHom := rfl

def t (j : Fin 3) : S j := smk j (X 3)
def u (j : Fin 3) : S j := smk j (upoly j)
lemma source_t_sq (j : Fin 3) : t j^2=baseMap j (b j) := by
  have h:=congrArg (smk j) (source_b_identity j)
  simpa only [map_sub,map_mul,map_add,map_neg,map_pow,srelation,zero_add,add_zero,neg_zero,mul_zero,sub_zero,zero_sub,sub_self,sub_eq_zero,t,b,baseMap_rq] using h
lemma source_ut (j : Fin 3) : u j*t j=baseMap j (c j) := by
  have h:=congrArg (smk j) (source_c_identity j)
  have hb : smk j (X 3^2-subst j (bpoly j))=0 := by
    rw [map_sub,map_pow]
    exact sub_eq_zero.mpr (by simpa only [t,b,baseMap_rq] using source_t_sq j)
  simpa only [map_sub,map_add,map_mul,map_neg,srelation,zero_add,neg_zero,sub_self,mul_zero,hb,zero_add,add_zero,sub_eq_zero,u,t,c,baseMap_rq] using h
lemma source_u_sq (j : Fin 3) : u j^2=baseMap j (a j) := by
  have h:=congrArg (smk j) (source_a_identity j)
  have hb : smk j (X 3^2-subst j (bpoly j))=0 := by
    rw [map_sub,map_pow]
    exact sub_eq_zero.mpr (by simpa only [t,b,baseMap_rq] using source_t_sq j)
  simpa only [map_sub,map_mul,map_neg,map_pow,srelation,neg_zero,mul_zero,hb,sub_zero,sub_eq_zero,u,a,baseMap_rq] using h
lemma source_unit (j : Fin 3) : u j^2+algebraMap ℚ (S j) (lambda j)*t j^2=1 := by
  rw [source_u_sq,source_t_sq]
  have h:=congrArg (baseMap j) (base_unit_ideal j)
  simpa only [map_add,map_mul,map_one,AlgHom.commutes] using h
end FourCorner.ThetaChartAlgebras
#print axioms FourCorner.ThetaChartAlgebras.baseMap
#print axioms FourCorner.ThetaChartAlgebras.source_t_sq
#print axioms FourCorner.ThetaChartAlgebras.source_ut
#print axioms FourCorner.ThetaChartAlgebras.source_u_sq
#print axioms FourCorner.ThetaChartAlgebras.source_unit
