import ThetaLiteralModels
import ThetaModelBase
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace FourCorner.ThetaTargetSmooth
open Algebra AlgebraicGeometry MvPolynomial CategoryTheory
open ThetaLiteralModels
universe u
variable {k : Type u} [Field k] [CharZero k]
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
lemma drop_table (j a : Fin 3) : ThetaAmbientChart.drop 2 j a =
    ![![0,0,1],![0,0,1],![0,1,0]] j a := by
  fin_cases j <;> fin_cases a <;> decide
abbrev ae := ThetaQuotientChart.affineEquation (targetEquation k)
abbrev ar := ThetaQuotientChart.affineRing (targetEquation k)
def ax (j : Fin 3) (a : Fin 2) : ar (k:=k) j := Ideal.Quotient.mk _ (X a)
def columns (a : Fin 2) (_ : Fin 1) : Fin 2 := a
lemma columns_injective (a : Fin 2) : Function.Injective (columns a) := by intro x y _; exact Subsingleton.elim _ _
def pres (j : Fin 3) (a : Fin 2) : PreSubmersivePresentation k (ar (k:=k) j) (Fin 2) (Fin 1) :=
  .naive (v:=ae j) (columns a) (columns_injective a)
@[simp] lemma pderiv_nat (a : Fin 2) (n : ℕ) : pderiv a (n : MvPolynomial (Fin 2) k)=0 := by
  have h := (MvPolynomial.pderiv_C (i:=a) (a:=(n:k)))
  simpa only [map_natCast] using h
lemma jacobi (j : Fin 3) (a : Fin 2) :
    (pres (k:=k) j a).jacobiMatrix=fun r c=>pderiv (columns a r) (ae j c) := by
  apply Matrix.ext
  intro r c
  exact PreSubmersivePresentation.jacobiMatrix_apply (pres (k:=k) j a) r c
lemma pres_map (j : Fin 3) (a : Fin 2) (p : MvPolynomial (Fin 2) k) :
    algebraMap (pres j a).Ring (ar j) p=Ideal.Quotient.mk _ p := rfl

def eqScalar {F : Type*} [CommRing F] (j : Fin 3) (_ : Fin 1) (x : Fin 2 → F) : F :=
  ![9801*(x 0)^4 + 19598*(x 0)^2 + 39984*(x 1)^4 - (x 1)^2*(39592*(x 0)^2 + 39592) + 9801,
    9801*(x 0)^4 + 19598*(x 0)^2 + 39984*(x 1)^4 - (x 1)^2*(39592*(x 0)^2 + 39592) + 9801,
    9801*(x 0)^4 + 19598*(x 0)^2*(x 1)^2 - 39592*(x 0)^2 + 9801*(x 1)^4 - 39592*(x 1)^2 + 39984] j
def minorScalar {F : Type*} [CommRing F] (j : Fin 3) (a : Fin 2) (x : Fin 2 → F) : F :=
  ![![39204*(x 0)^3 - 79184*(x 0)*(x 1)^2 + 39196*(x 0), 159936*(x 1)^3 - 2*(x 1)*(39592*(x 0)^2 + 39592)],
    ![39204*(x 0)^3 - 79184*(x 0)*(x 1)^2 + 39196*(x 0), 159936*(x 1)^3 - 2*(x 1)*(39592*(x 0)^2 + 39592)],
    ![39204*(x 0)^3 + 39196*(x 0)*(x 1)^2 - 79184*(x 0), 39196*(x 0)^2*(x 1) + 39204*(x 1)^3 - 79184*(x 1)]] j a
lemma relations {F : Type u} [Field F] [Algebra k F] (j : Fin 3) (f : ar (k:=k) j →ₐ[k] F) :
    ∀ a, eqScalar j a (fun b=>f (ax j b))=0 := by
  intro a
  have h : Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (targetEquation k) j) (ae j a)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,rfl⟩)
  have h' := congrArg f h
  have hc (c : k) : f (Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (targetEquation k) j) (C c))=algebraMap k F c := f.commutes c
  fin_cases j <;> fin_cases a
  all_goals simp [ae,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,targetEquation,targetPolynomial,drop_table,
      map_ofNat,hc,map_natCast] at h'
  all_goals simp [eqScalar,ax]
  all_goals linear_combination h'
lemma jacobian_formula {F : Type u} [Field F] [Algebra k F] (j : Fin 3) (a : Fin 2) (f : ar (k:=k) j →ₐ[k] F) :
    f (pres j a).jacobian=minorScalar j a (fun b=>f (ax j b)) := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,pres_map,jacobi,Matrix.det_fin_one]
  have hc (c : k) : f (Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (targetEquation k) j) (C c))=algebraMap k F c := f.commutes c
  have hn9801 (a : Fin 2) : pderiv a (9801 : MvPolynomial (Fin 2) k)=0 := by
    have h := (MvPolynomial.pderiv_C (i:=a) (a:=(9801:k)))
    simpa only [map_ofNat] using h
  have hn19598 (a : Fin 2) : pderiv a (19598 : MvPolynomial (Fin 2) k)=0 := by
    have h := (MvPolynomial.pderiv_C (i:=a) (a:=(19598:k)))
    simpa only [map_ofNat] using h
  have hn39592 (a : Fin 2) : pderiv a (39592 : MvPolynomial (Fin 2) k)=0 := by
    have h := (MvPolynomial.pderiv_C (i:=a) (a:=(39592:k)))
    simpa only [map_ofNat] using h
  have hn39984 (a : Fin 2) : pderiv a (39984 : MvPolynomial (Fin 2) k)=0 := by
    have h := (MvPolynomial.pderiv_C (i:=a) (a:=(39984:k)))
    simpa only [map_ofNat] using h
  fin_cases j <;> fin_cases a
  all_goals simp [ae,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,targetEquation,targetPolynomial,drop_table,
      columns,hn9801,hn19598,hn39592,hn39984,pderiv_nat,pderiv_pow,map_ofNat,hc,map_natCast,minorScalar,ax]
  all_goals ring

lemma field_jacobian (j : Fin 3) (F : Type u) [Field F] [Algebra k F] (f : ar (k:=k) j →ₐ[k] F) :
    ∃ a, f (pres j a).jacobian≠0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  by_contra hn
  push_neg at hn
  have he := relations j f
  have hm (a : Fin 2) : minorScalar j a (fun b=>f (ax j b))=0 := by rw [← jacobian_formula]; exact hn a
  have h0:=he 0
  have m0:=hm 0;have m1:=hm 1
  let x : Fin 2 → F := fun b=>f (ax j b)
  change eqScalar j 0 x=0 at h0
  change minorScalar j 0 x=0 at m0
  change minorScalar j 1 x=0 at m1
  fin_cases j
  · change 9801*(x 0)^4 + 19598*(x 0)^2 + 39984*(x 1)^4 - (x 1)^2*(39592*(x 0)^2 + 39592) + 9801=0 at h0
    change 39204*(x 0)^3 - 79184*(x 0)*(x 1)^2 + 39196*(x 0)=0 at m0
    change 159936*(x 1)^3 - 2*(x 1)*(39592*(x 0)^2 + 39592)=0 at m1
    have hunit : (1:F)=0 := by
      linear_combination (((1 / 9801) + ((168266 / 3267) * ((x 1) ^ 2)) + ((970201 / 38416) * ((x 0) ^ 4)) + ((470644019999 / 18825760800) * ((x 0) ^ 2)) + ((-1665835117 / 32016600) * ((x 0) ^ 2) * ((x 1) ^ 2))))*h0 +
        ((((-945993999949 / 75303043200) * ((x 0) ^ 3)) + ((-470743921201 / 75303043200) * (x 0)) + ((-970201 / 153664) * ((x 0) ^ 5)) + ((-84133 / 6534) * (x 0) * ((x 1) ^ 2)) + ((1665835117 / 128066400) * ((x 0) ^ 3) * ((x 1) ^ 2))))*m0 +
        ((((-84133 / 6534) * ((x 1) ^ 3)) + ((499847 / 78408) * (x 1)) + ((-4977073019 / 392203350) * (x 1) * ((x 0) ^ 2)) + ((-970201 / 153664) * (x 1) * ((x 0) ^ 4)) + ((1665835117 / 128066400) * ((x 0) ^ 2) * ((x 1) ^ 3))))*m1
    exact one_ne_zero hunit
  · change 9801*(x 0)^4 + 19598*(x 0)^2 + 39984*(x 1)^4 - (x 1)^2*(39592*(x 0)^2 + 39592) + 9801=0 at h0
    change 39204*(x 0)^3 - 79184*(x 0)*(x 1)^2 + 39196*(x 0)=0 at m0
    change 159936*(x 1)^3 - 2*(x 1)*(39592*(x 0)^2 + 39592)=0 at m1
    have hunit : (1:F)=0 := by
      linear_combination (((1 / 9801) + ((168266 / 3267) * ((x 1) ^ 2)) + ((970201 / 38416) * ((x 0) ^ 4)) + ((470644019999 / 18825760800) * ((x 0) ^ 2)) + ((-1665835117 / 32016600) * ((x 0) ^ 2) * ((x 1) ^ 2))))*h0 +
        ((((-945993999949 / 75303043200) * ((x 0) ^ 3)) + ((-470743921201 / 75303043200) * (x 0)) + ((-970201 / 153664) * ((x 0) ^ 5)) + ((-84133 / 6534) * (x 0) * ((x 1) ^ 2)) + ((1665835117 / 128066400) * ((x 0) ^ 3) * ((x 1) ^ 2))))*m0 +
        ((((-84133 / 6534) * ((x 1) ^ 3)) + ((499847 / 78408) * (x 1)) + ((-4977073019 / 392203350) * (x 1) * ((x 0) ^ 2)) + ((-970201 / 153664) * (x 1) * ((x 0) ^ 4)) + ((1665835117 / 128066400) * ((x 0) ^ 2) * ((x 1) ^ 3))))*m1
    exact one_ne_zero hunit
  · change 9801*(x 0)^4 + 19598*(x 0)^2*(x 1)^2 - 39592*(x 0)^2 + 9801*(x 1)^4 - 39592*(x 1)^2 + 39984=0 at h0
    change 39204*(x 0)^3 + 39196*(x 0)*(x 1)^2 - 79184*(x 0)=0 at m0
    change 39196*(x 0)^2*(x 1) + 39204*(x 1)^3 - 79184*(x 1)=0 at m1
    have hunit : (1:F)=0 := by
      linear_combination (((1 / 39984) + ((-1070701 / 319872) * ((x 0) ^ 2)) + ((329967 / 106624) * ((x 1) ^ 2)) + ((33326667 / 10449152) * ((x 0) ^ 4)) + ((-33326667 / 10449152) * ((x 0) ^ 2) * ((x 1) ^ 2))))*h0 +
        ((((-33326667 / 41796608) * ((x 0) ^ 5)) + ((-540655 / 319872) * (x 0)) + ((447329 / 182784) * ((x 0) ^ 3)) + ((-329967 / 426496) * (x 0) * ((x 1) ^ 2)) + ((33326667 / 41796608) * ((x 0) ^ 3) * ((x 1) ^ 2))))*m0 +
        ((((-329967 / 426496) * ((x 1) ^ 3)) + ((499847 / 319872) * (x 1)) + ((-33326667 / 41796608) * (x 1) * ((x 0) ^ 4)) + ((-329967 / 426496) * (x 1) * ((x 0) ^ 2)) + ((33326667 / 41796608) * ((x 0) ^ 2) * ((x 1) ^ 3))))*m1
    exact one_ne_zero hunit
theorem affine_smooth (j : Fin 3) : SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k (ar (k:=k) j)))) := by
  have hs := FiniteJacobianSmooth.jacobian_span_of_field_points (pres (k:=k) j) (field_jacobian (k:=k) j)
  simpa using FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres (k:=k) j) hs
/-- Actual native scheme smoothness of the literal plane quartic in P2, on all three charts. -/
theorem target_smooth : SmoothOfRelativeDimension 1 (dToBase k) :=
  ThetaModelBase.smooth _ _ affine_smooth
end FourCorner.ThetaTargetSmooth
#print axioms FourCorner.ThetaTargetSmooth.field_jacobian
#print axioms FourCorner.ThetaTargetSmooth.target_smooth
