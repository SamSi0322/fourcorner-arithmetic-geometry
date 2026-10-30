import ThetaCoverClassPortable.ThetaChartAlgebras
noncomputable section
namespace FourCorner.ThetaSourcePresentation
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaQuotientCharts ThetaChartAlgebras
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

def beta (j i : Fin 3) : ℚ :=
  match j,i with
  | 0,0=> -50 | 0,1=> -51 | 0,2=> -51
  | 1,0=> -99 | 1,1=> -2 | 1,2=> -198
  | 2,0=> -99 | 2,1=> -198 | 2,2=> -2
def gamma (j i : Fin 3) : ℚ :=
  match j,i with
  | 0,0=>0 | 0,1=> -14 | 0,2=>14
  | 1,0=>14 | 1,1=>0 | 1,2=>28
  | 2,0=> -14 | 2,1=> -28 | 2,2=>0
lemma inverse_identity (j i : Fin 3) : se j i=
    -(upoly j^2-subst j (apoly j))+
      C (beta j i)*(X 3^2-subst j (bpoly j))+
      C (gamma j i)*(upoly j*X 3-subst j (cpoly j)) := by
  rw [source_equation_formula]
  fin_cases j <;> fin_cases i
  all_goals apply MvPolynomial.funext
  all_goals intro x
  all_goals norm_num [subst,aeval_def,basePolys,rcoords,scoords,seFormula,upoly,
    apoly,bpoly,cpoly,shift,lambda,beta,gamma,map_ofNat]
  all_goals ring

def baseInverse (j : Fin 3) (i : Fin 2) : Fin 2 := if j=0 then i else i.rev
lemma base_coordinate (j : Fin 3) (i : Fin 2) :
    smk j (X i.castSucc.castSucc)=baseMap j (rq j (X (baseInverse j i))) := by
  rw [baseMap_rq]
  fin_cases j <;> fin_cases i
  all_goals simp [subst,basePolys,baseInverse]
lemma z_coordinate (j : Fin 3) : smk j (X 2)=u j-algebraMap ℚ (S j) (shift j)*t j := by
  change smk j (X 2)=u j-smk j (C (shift j))*t j
  simp [u,upoly,t]

section Values
variable (j : Fin 3) {V : Type*} [CommRing V] [Algebra (R j) V] [Algebra ℚ V]
  [IsScalarTower ℚ (R j) V]
def structural : R j →ₐ[ℚ] V := (Algebra.ofId (R j) V).restrictScalars ℚ
def values (v w : V) : Fin 4 → V
  | 0=>(structural j) (rq j (X (baseInverse j 0)))
  | 1=>(structural j) (rq j (X (baseInverse j 1)))
  | 2=>v-algebraMap ℚ V (shift j)*w
  | 3=>w
lemma eval_subst (v w : V) (p : RA) :
    aeval (values j v w) (subst j p)=structural j (rq j p) := by
  have h : (aeval (values j v w)).comp (subst j)=(structural j).comp (rq j) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases j <;> fin_cases i
    all_goals simp [AlgHom.comp_apply,subst,basePolys,values,baseInverse]
  exact DFunLike.congr_fun h p
lemma eval_u (v w : V) : aeval (values j v w) (upoly j)=v := by
  simp [upoly,values]
lemma eval_t (v w : V) : aeval (values j v w) (X 3 : SA)=w := by simp [values]

def ofUT (v w : V)
    (hv : v^2=algebraMap (R j) V (a j))
    (hw : w^2=algebraMap (R j) V (b j))
    (hc : v*w=algebraMap (R j) V (c j)) : S j →ₐ[ℚ] V :=
  Ideal.Quotient.liftₐ _ (aeval (values j v w)) (by
    have hh : ThetaQuotientChart.affineIdeal (ThetaLiteralModels.sourceEquation ℚ) (sourceIndex j)≤
        RingHom.ker (aeval (values j v w)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change aeval (values j v w) (se j i)=0
      rw [inverse_identity]
      simp only [map_add,map_neg,map_mul,map_sub,map_pow,aeval_C,eval_subst,eval_u,eval_t]
      change -(v^2-algebraMap (R j) V (a j))+
        algebraMap ℚ V (beta j i)*(w^2-algebraMap (R j) V (b j))+
        algebraMap ℚ V (gamma j i)*(v*w-algebraMap (R j) V (c j))=0
      rw [hv,hw,hc]
      ring
    exact fun x hx=>hh hx)
@[simp] lemma ofUT_smk (v w : V) (hv) (hw) (hc) (p : SA) :
    ofUT j v w hv hw hc (smk j p)=aeval (values j v w) p := rfl
lemma ofUT_base (v w : V) (hv) (hw) (hc) (r : R j) :
    ofUT j v w hv hw hc (baseMap j r)=algebraMap (R j) V r := by
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective r
  change ofUT j v w hv hw hc (baseMap j (rq j p))=_
  rw [baseMap_rq,ofUT_smk,eval_subst]
  rfl
/-- Universal R-algebra map from the literal source chart, obtained from u²=A,t²=B,ut=C. -/
def ofUTR (v w : V) (hv : v^2=algebraMap (R j) V (a j))
    (hw : w^2=algebraMap (R j) V (b j)) (hc : v*w=algebraMap (R j) V (c j)) : S j →ₐ[R j] V :=
  { (ofUT j v w hv hw hc).toRingHom with commutes':=ofUT_base j v w hv hw hc }
@[simp] lemma ofUTR_u (v w : V) (hv) (hw) (hc) : ofUTR j v w hv hw hc (u j)=v := by
  change ofUT j v w hv hw hc (smk j (upoly j))=v
  rw [ofUT_smk,eval_u]
@[simp] lemma ofUTR_t (v w : V) (hv) (hw) (hc) : ofUTR j v w hv hw hc (t j)=w := by
  change ofUT j v w hv hw hc (smk j (X 3))=w
  rw [ofUT_smk,eval_t]

lemma hom_ext {f g : S j →ₐ[R j] V} (hu : f (u j)=g (u j)) (ht : f (t j)=g (t j)) : f=g := by
  have hx (i : Fin 4) : f (smk j (X i))=g (smk j (X i)) := by
    fin_cases i
    · change f (smk j (X (0:Fin 4)))=g (smk j (X (0:Fin 4)))
      have hb0 : smk j (X (0:Fin 4))=baseMap j (rq j (X (baseInverse j 0))) := base_coordinate j 0
      rw [hb0]
      exact (f.commutes _).trans (g.commutes _).symm
    · change f (smk j (X (1:Fin 4)))=g (smk j (X (1:Fin 4)))
      have hb1 : smk j (X (1:Fin 4))=baseMap j (rq j (X (baseInverse j 1))) := base_coordinate j 1
      rw [hb1]
      exact (f.commutes _).trans (g.commutes _).symm
    · change f (smk j (X (2:Fin 4)))=g (smk j (X (2:Fin 4)))
      rw [z_coordinate,map_sub,map_sub,map_mul,map_mul,ht,hu]
      have hcf : f (algebraMap ℚ (S j) (shift j))=algebraMap ℚ V (shift j) :=
        (f.restrictScalars ℚ).commutes _
      have hcg : g (algebraMap ℚ (S j) (shift j))=algebraMap ℚ V (shift j) :=
        (g.restrictScalars ℚ).commutes _
      rw [hcf,hcg]
    · exact ht
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C q => exact ((f.restrictScalars ℚ).commutes q).trans ((g.restrictScalars ℚ).commutes q).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    have hxi : f (Ideal.Quotient.mk _ (X i))=g (Ideal.Quotient.mk _ (X i)) := by
      change f (smk j (X i))=g (smk j (X i))
      exact hx i
    simpa only [map_mul] using congrArg₂ (·*·) hp hxi
end Values
end FourCorner.ThetaSourcePresentation
#print axioms FourCorner.ThetaSourcePresentation.ofUTR
#print axioms FourCorner.ThetaSourcePresentation.hom_ext
