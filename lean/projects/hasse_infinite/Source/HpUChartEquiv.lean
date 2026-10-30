import HpUChartTower

namespace FourCorner.HpUChartEquiv
open Polynomial MvPolynomial HpLiteralProjective HpLiteralSmooth HpUChartTower
open Multiquadratic.CoordinateAlgebra Multiquadratic.CoordinateUniversal
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

abbrev B (p : K) := HpLiteralProjective.affineRing K p 1
abbrev x (p : K) (i : Fin 4) : B K p := Ideal.Quotient.mk _ (MvPolynomial.X i)
def base (p : K) : K[X] →+* B K p := Polynomial.eval₂RingHom (algebraMap K (B K p)) (x K p 0)
@[simp] lemma base_C (p c : K) : base K p (Polynomial.C c)=algebraMap K (B K p) c := Polynomial.eval₂_C _ _
@[simp] lemma base_X (p : K) : base K p Polynomial.X=x K p 0 := Polynomial.eval₂_X _ _

 theorem relations (p : K) (i : Fin 3) :
    algebraMap K (B K p) p*(x K p i.succ)^2=base K p (qTimes K p i) := by
  have h : Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal (equation K p) 1)
      (ThetaQuotientChart.affineEquation (equation K p) 1 i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  let g : MvPolynomial (Fin 4) K →+* B K p := Ideal.Quotient.mk _
  have h' : g (ThetaQuotientChart.affineEquation (equation K p) 1 i)=0 := h
  have hc (c : K) : g (MvPolynomial.C c)=algebraMap K (B K p) c := rfl
  fin_cases i
  all_goals simp [ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,drop_table,
    qTimes,base,Polynomial.coe_eval₂RingHom,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,hc] at h'
  all_goals simp [qTimes,base,Polynomial.coe_eval₂RingHom,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,x]
  all_goals linear_combination h'

 theorem rootCondition (p : K) (hp : p ≠ 0) (i : Fin 3) :
    (x K p i.succ)^2=base K p (q K p i) := by
  have hunit : IsUnit (algebraMap K (B K p) p) := (isUnit_iff_ne_zero.mpr hp).map _
  apply hunit.mul_left_cancel
  rw [relations]
  have h := congrArg (base K p) (q_times_p K p hp i)
  simpa only [map_mul,base_C] using h.symm

 def toB (p : K) (hp : p ≠ 0) : Tower K p →+* B K p :=
  Multiquadratic.CoordinateUniversal.lift K[X] (B K p) (base K p)
    (q K p 0) (q K p 1) (q K p 2) (x K p 1) (x K p 2) (x K p 3)
    (rootCondition K p hp 0) (rootCondition K p hp 1) (rootCondition K p hp 2)

 theorem toB_base (p : K) (hp : p ≠ 0) (a : K[X]) :
    toB K p hp (algebraMap K[X] (Tower K p) a)=base K p a := lift_algebraMap _ _ _ _ _ _ _ _ _ _ _ _ a
 theorem toB_roots (p : K) (hp : p ≠ 0) (i : Fin 3) : toB K p hp (roots K p i)=x K p i.succ := by
  fin_cases i
  · exact lift_coordinate₁ _ _ _ _ _ _ _ _ _ _ _ _
  · exact lift_coordinate₂ _ _ _ _ _ _ _ _ _ _ _ _
  · exact lift_coordinate₃ _ _ _ _ _ _ _ _ _ _ _ _

 def values (p : K) : Fin 4 → Tower K p := ![z K p,roots K p 0,roots K p 1,roots K p 2]
 def evalA (p : K) : MvPolynomial (Fin 4) K →+* Tower K p := MvPolynomial.eval₂Hom (coeff K p) (values K p)
 theorem evalA_relations (p : K) (hp : p ≠ 0) (i : Fin 3) :
    evalA K p (ThetaQuotientChart.affineEquation (equation K p) 1 i)=0 := by
  have hmul (i : Fin 3) : coeff K p p*(roots K p i)^2=algebraMap K[X] (Tower K p) (qTimes K p i) := by
    rw [roots_sq]
    change algebraMap K[X] (Tower K p) (Polynomial.C p)*algebraMap K[X] (Tower K p) (q K p i)=_
    rw [← map_mul,q_times_p K p hp i]
  have h0:=hmul 0
  have h1:=hmul 1
  have h2:=hmul 2
  have hc (c : K) : algebraMap K[X] (Tower K p) (Polynomial.C c)=coeff K p c := rfl
  simp only [qTimes,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,hc] at h0 h1 h2
  fin_cases i
  all_goals simp [evalA,values,z,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,equation,drop_table,
      map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]
  · linear_combination h0
  · linear_combination h1
  · linear_combination h2

 def toA (p : K) (hp : p ≠ 0) : B K p →+* Tower K p :=
  Ideal.Quotient.lift _ (evalA K p) (by
    have hk : ThetaQuotientChart.affineIdeal (equation K p) 1 ≤ RingHom.ker (evalA K p) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact evalA_relations K p hp i
    exact fun a ha=>hk ha)
 @[simp] theorem toA_X (p : K) (hp : p ≠ 0) (i : Fin 4) : toA K p hp (x K p i)=values K p i := MvPolynomial.eval₂_X _ _ _
 @[simp] theorem toA_C (p : K) (hp : p ≠ 0) (c : K) :
    toA K p hp (algebraMap K (B K p) c)=coeff K p c := MvPolynomial.eval₂_C _ _ _

 theorem toA_base (p : K) (hp : p ≠ 0) :
    (toA K p hp).comp (base K p)=algebraMap K[X] (Tower K p) := by
  apply Polynomial.ringHom_ext
  · intro c
    simpa only [RingHom.comp_apply,base,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,HpUChartTower.coeff]
      using toA_C K p hp c
  · simpa [RingHom.comp_apply,base,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,values,z]
      using toA_X K p hp 0

 theorem from_to (p : K) (hp : p ≠ 0) : (toB K p hp).comp (toA K p hp)=RingHom.id (B K p) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change toB K p hp (toA K p hp (algebraMap K (B K p) c))=algebraMap K (B K p) c
    rw [toA_C]
    change toB K p hp (algebraMap K[X] (Tower K p) (Polynomial.C c))=_
    rw [toB_base,base_C]
  · intro i
    change toB K p hp (toA K p hp (x K p i))=x K p i
    rw [toA_X]
    fin_cases i
    · change toB K p hp (algebraMap K[X] (Tower K p) Polynomial.X)=_
      rw [toB_base,base_X]
      rfl
    · exact toB_roots K p hp 0
    · exact toB_roots K p hp 1
    · exact toB_roots K p hp 2

 theorem to_from (p : K) (hp : p ≠ 0) : (toA K p hp).comp (toB K p hp)=RingHom.id (Tower K p) := by
  apply Multiquadratic.CoordinateUniversal.ringHom_ext K[X] (Tower K p)
  · intro a
    change toA K p hp (toB K p hp (algebraMap K[X] (Tower K p) a))=algebraMap K[X] (Tower K p) a
    rw [toB_base]
    exact RingHom.congr_fun (toA_base K p hp) a
  · change toA K p hp (toB K p hp (roots K p 0))=roots K p 0
    rw [toB_roots,toA_X];rfl
  · change toA K p hp (toB K p hp (roots K p 1))=roots K p 1
    rw [toB_roots,toA_X];rfl
  · change toA K p hp (toB K p hp (roots K p 2))=roots K p 2
    rw [toB_roots,toA_X];rfl

 def ringEquiv (p : K) (hp : p ≠ 0) : B K p ≃+* Tower K p where
  __ := toA K p hp
  invFun := toB K p hp
  left_inv a := RingHom.congr_fun (from_to K p hp) a
  right_inv a := RingHom.congr_fun (to_from K p hp) a

 theorem z_regular (p : K) (hp : p ≠ 0) : IsRegular (x K p 0) := by
  have hr := HpUChartTower.z_regular K p
  have he : ringEquiv K p hp (x K p 0)=z K p := toA_X K p hp 0
  have hi : Function.Injective (fun a : B K p=>x K p 0*a) := by
    intro a b hab
    apply (ringEquiv K p hp).injective
    apply hr.left
    change z K p*(ringEquiv K p hp) a=z K p*(ringEquiv K p hp) b
    rw [← he,← map_mul,← map_mul]
    exact congrArg (ringEquiv K p hp) hab
  exact ⟨hi,fun a b hab=>hi (by simpa only [mul_comm] using hab)⟩

#print axioms ringEquiv
#print axioms z_regular
end
end FourCorner.HpUChartEquiv
