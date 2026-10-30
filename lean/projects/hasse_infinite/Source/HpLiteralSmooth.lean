import HpNoTwoCoordinatesZero
import ThetaModelBase

namespace FourCorner.HpLiteralSmooth
open Algebra AlgebraicGeometry MvPolynomial CategoryTheory HpLiteralProjective
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

lemma drop_table (j a : Fin 5) : ThetaAmbientChart.drop 4 j a =
    ![![0,0,1,2,3],![0,0,1,2,3],![0,1,0,2,3],![0,1,2,0,3],![0,1,2,3,0]] j a := by
  fin_cases j <;> fin_cases a <;> decide

def columns : Fin 4 → Fin 3 → Fin 4
  | 0 => ![1,2,3]
  | 1 => ![0,2,3]
  | 2 => ![0,1,3]
  | 3 => ![0,1,2]
lemma columns_injective (a : Fin 4) : Function.Injective (columns a) := by fin_cases a <;> decide
lemma columns_ne (a : Fin 4) (i : Fin 3) : columns a i ≠ a := by fin_cases a <;> fin_cases i <;> decide

abbrev ae (p : K) := ThetaQuotientChart.affineEquation (equation K p)
abbrev ar (p : K) := ThetaQuotientChart.affineRing (equation K p)
def ax (p : K) (j : Fin 5) (a : Fin 4) : ar p j := Ideal.Quotient.mk _ (X a)
def pres (p : K) (j : Fin 5) (a : Fin 4) :
    PreSubmersivePresentation K (ar p j) (Fin 4) (Fin 3) :=
  .naive (v:=ae p j) (columns a) (columns_injective a)

@[simp] lemma map_C (p : K) (j : Fin 5) {F : Type u} [Field F] [Algebra K F]
    (f : ar p j →ₐ[K] F) (c : K) :
    f (Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (equation K p) j) (C c))=algebraMap K F c :=
  f.commutes c
@[simp] lemma map_quot_C {I : Ideal (MvPolynomial (Fin 4) K)}
    {F : Type u} [Field F] [Algebra K F] (f : (MvPolynomial (Fin 4) K ⧸ I) →ₐ[K] F) (c : K) :
    f (Ideal.Quotient.mk I (C c))=algebraMap K F c := f.commutes c
@[simp] lemma pderiv_nat (a : Fin 4) (n : ℕ) : pderiv a (n : MvPolynomial (Fin 4) K)=0 := by
  have h := (MvPolynomial.pderiv_C (i:=a) (a:=(n:K)))
  simpa only [map_natCast] using h

def extend {F : Type*} [CommRing F] (j : Fin 5) (x : Fin 4 → F) (a : Fin 5) : F :=
  if a=j then 1 else x (ThetaAmbientChart.drop 4 j a)
lemma extend_self {F : Type*} [CommRing F] (j : Fin 5) (x : Fin 4 → F) : extend j x j=1 := if_pos rfl
lemma extend_insert {F : Type*} [CommRing F] (j : Fin 5) (x : Fin 4 → F) (a : Fin 4) :
    extend j x (ThetaAmbientChart.insert 4 j a)=x a := by
  rw [extend,if_neg (ThetaAmbientChart.insert_ne 4 j a),ThetaAmbientChart.drop_insert]

def scalar {F : Type*} [CommRing F] (p : F) : Fin 5 → Fin 4 → F :=
 ![![8*p^3,-16*p^2*(p-1),16*p^2*(p+1),-8*p^2*(p-1)],
   ![8*p^3,16*p^3*(p-1),16*p^3*(p+1),-8*p^3*(p+1)],
   ![-16*p^2*(p-1),16*p^3*(p-1),-64*p^2*(p-1)*(p+1),32*p^3*(p-1)],
   ![16*p^2*(p+1),16*p^3*(p+1),-64*p^2*(p-1)*(p+1),-32*p^2*(p+1)],
   ![-8*p^2*(p-1),-8*p^3*(p+1),32*p^3*(p-1),-32*p^2*(p+1)]]

theorem scalar_ne_zero {F : Type*} [Field F] [CharZero F] (p : F)
    (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (j : Fin 5) (a : Fin 4) : scalar p j a ≠ 0 := by
  fin_cases j <;> fin_cases a <;> simp [scalar,mul_ne_zero,hp,ha,hb]

lemma relations (p : K) (j : Fin 5) {F : Type u} [Field F] [Algebra K F] [CharZero F]
    (f : ar p j →ₐ[K] F) : CompleteSource11.Source (algebraMap K F p)
      (extend j (fun a=>f (ax p j a)) 0) (extend j (fun a=>f (ax p j a)) 1)
      (extend j (fun a=>f (ax p j a)) 2) (extend j (fun a=>f (ax p j a)) 3)
      (extend j (fun a=>f (ax p j a)) 4) := by
  apply (homogeneous_equations F _ _).mp
  intro i
  have h : Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (equation K p) j) (ae p j i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  let g : MvPolynomial (Fin 4) K →+* F := f.toRingHom.comp (Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (equation K p) j))
  have h' : g (ae p j i)=0 := by simpa only [g,RingHom.comp_apply,AlgHom.coe_toRingHom,AlgHom.toRingHom_eq_coe,map_zero] using congrArg f h
  have hc (c : K) : g (C c)=algebraMap K F c := f.commutes c
  change eval (extend j (fun a=>g (X a))) (equation F (algebraMap K F p) i)=0
  fin_cases j <;> fin_cases i
  all_goals simp [ae,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,drop_table,
      extend,ax,map_add,map_sub,map_mul,map_pow,map_zero,map_one,map_ofNat,hc,map_C,map_natCast] at h' ⊢
  all_goals linear_combination h'

lemma jacobian_formula (p : K) (j : Fin 5) (a : Fin 4) {F : Type u} [Field F] [Algebra K F]
    (f : ar p j →ₐ[K] F) : f (pres p j a).jacobian=
      scalar (algebraMap K F p) j a *f (ax p j (columns a 0))*f (ax p j (columns a 1))*f (ax p j (columns a 2)) := by
  have hj : (pres p j a).jacobiMatrix=fun r c=>pderiv (columns a r) (ae p j c) := by
    apply Matrix.ext
    intro r c
    exact PreSubmersivePresentation.jacobiMatrix_apply (pres p j a) r c
  let g : MvPolynomial (Fin 4) K →+* F := f.toRingHom.comp (Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (equation K p) j))
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  change g (Matrix.det (pres p j a).jacobiMatrix)=
    scalar (algebraMap K F p) j a*g (X (columns a 0))*g (X (columns a 1))*g (X (columns a 2))
  rw [hj,Matrix.det_fin_three]
  have hc (c : K) : g (C c)=algebraMap K F c := f.commutes c
  have hn2 (b : Fin 4) : pderiv b (2 : MvPolynomial (Fin 4) K)=0 := pderiv_nat b 2
  fin_cases j <;> fin_cases a
  all_goals simp [ae,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,drop_table,
      columns,pderiv_pow,pderiv_nat,hn2,map_add,map_sub,map_mul,map_pow,map_zero,map_one,map_ofNat,hc,map_C,map_natCast,scalar,ax]
  all_goals ring

lemma field_jacobian (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (j : Fin 5) (F : Type u) [Field F] [Algebra K F] (f : ar p j →ₐ[K] F) :
    ∃a,f (pres p j a).jacobian ≠ 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hp' : algebraMap K F p ≠ 0 := (map_ne_zero _).mpr hp
  have ha' : algebraMap K F p-1 ≠ 0 := by simpa only [map_sub,map_one] using (map_ne_zero (algebraMap K F)).mpr ha
  have hb' : algebraMap K F p+1 ≠ 0 := by simpa only [map_add,map_one] using (map_ne_zero (algebraMap K F)).mpr hb
  let x (a : Fin 4) := f (ax p j a)
  have hn : ¬∀i,extend j x i=0 := by
    intro h
    have hh := h j
    rw [extend_self] at hh
    exact one_ne_zero hh
  have hpair := HpNoTwoCoordinatesZero.no_two_zero (algebraMap K F p) hp' ha' hb'
    (extend j x) (relations p j f) hn
  have hne (a b : Fin 4) (hab : a ≠ b) : x a=0 → x b=0 → False := by
    intro haz hbz
    apply hpair (ThetaAmbientChart.insert 4 j a) (ThetaAmbientChart.insert 4 j b)
      (fun h => hab (Fin.succAbove_right_injective h))
    · rwa [extend_insert]
    · rwa [extend_insert]
  have hchoose : ∃a : Fin 4,∀r : Fin 3,x (columns a r) ≠ 0 := by
    by_cases h : ∃a,x a=0
    · obtain ⟨a,ha0⟩ := h
      exact ⟨a,fun r hz=>hne (columns a r) a (columns_ne a r) hz ha0⟩
    · push_neg at h
      exact ⟨0,fun r=>h (columns 0 r)⟩
  obtain ⟨a,hnz⟩ := hchoose
  refine ⟨a,?_⟩
  rw [jacobian_formula]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (scalar_ne_zero _ hp' ha' hb' j a) (hnz 0)) (hnz 1)) (hnz 2)

theorem affine_smooth (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) (j : Fin 5) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap K (ar p j)))) := by
  have hs := FiniteJacobianSmooth.jacobian_span_of_field_points (pres p j) (field_jacobian p hp ha hb j)
  simpa using FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres p j) hs

/-- Genuine all-chart scheme smoothness of the EXACT three quadrics in P4
for every p with the original nondegenerate parameter conditions. -/
theorem smooth (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    SmoothOfRelativeDimension 1 (toBase K p) :=
  ThetaModelBase.smooth _ _ (affine_smooth p hp ha hb)

#print axioms HpNoTwoCoordinatesZero.no_two_zero
#print axioms scalar_ne_zero
#print axioms jacobian_formula
#print axioms field_jacobian
#print axioms smooth
end
end FourCorner.HpLiteralSmooth
