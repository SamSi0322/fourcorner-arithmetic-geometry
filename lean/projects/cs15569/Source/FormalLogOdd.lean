import EllipticCurves.WeierstrassFormalGroup.GroupLaw
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman

/-- On the literal short Weierstrass model, the actual formal inverse is -X. -/
theorem short_inverse {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (h1 : W.a₁=0) (h3 : W.a₃=0) : W.inverseSeries= -(PowerSeries.X : PowerSeries R) := by
  have hu : W.uSeries=1 := by simp [WeierstrassCurve.uSeries,h1,h3]
  have hi : PowerSeries.invOfUnit W.uSeries 1=1 := by
    have h := W.mul_invOfUnit_uSeries
    rw [hu,one_mul] at h
    simpa only [hu] using h
  rw [WeierstrassCurve.inverseSeries,hi,mul_one]

def negPair {R : Type*} [CommRing R] : Unit ⊕ Unit → MvPowerSeries Unit R :=
  Sum.elim (fun _ => X ()) (fun _ => -X ())

lemma hasSubst_negPair {R : Type*} [CommRing R] : HasSubst (negPair (R:=R)) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  cases s <;> simp [negPair]

/-- The inverse relation concerns the original chord addition series. -/
theorem short_inverse_substitution {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (h1 : W.a₁=0) (h3 : W.a₃=0) :
    subst (negPair (R:=R)) W.addSeries=0 := by
  have h := W.subst_inverseSeries_addSeries
  rw [short_inverse W h1 h3] at h
  exact h

/-- Additivity of the genuine formal logarithm forces oddness when the genuine
formal inverse is -X. It is not a freely chosen additive coordinate. -/
theorem formal_log_odd {K : Type*} [Field K] [CharZero K]
    (Phi : FormalGroupLaw K Unit) (hinv : subst (negPair (R:=K)) (Phi.F ())=0) :
    subst (fun _ : Unit => -(X () : MvPowerSeries Unit K)) (Phi.log ())= -Phi.log () := by
  have hp := hasSubst_negPair (R:=K)
  have hleft : subst (negPair (R:=K)) (subst Phi.F (Phi.log ()))=0 := by
    rw [subst_comp_subst_apply (FormalGroupLaw.hasSubst_F Phi) hp]
    have hf : (fun j : Unit => subst (negPair (R:=K)) (Phi.F j))=(fun _ : Unit => (0:MvPowerSeries Unit K)) := by
      funext j
      cases j
      exact hinv
    rw [hf]
    change subst (0 : Unit → MvPowerSeries Unit K) (Phi.log ())=0
    exact subst_zero_of_constantCoeff_zero (Phi.constantCoeff_log ())
  have hX : subst (negPair (R:=K))
      (subst (fun s : Unit => (X (Sum.inl s):MvPowerSeries (Unit⊕Unit) K)) (Phi.log ()))=Phi.log () := by
    rw [subst_comp_subst_apply FormalGroupLaw.hasSubst_Xemb hp]
    have hf : (fun s : Unit => subst (negPair (R:=K))
        (X (Sum.inl s) : MvPowerSeries (Unit⊕Unit) K))=(X : Unit → MvPowerSeries Unit K) := by
      funext s
      rw [subst_X hp]
      cases s
      rfl
    rw [hf,subst_self]
    rfl
  have hY : subst (negPair (R:=K))
      (subst (fun s : Unit => (X (Sum.inr s):MvPowerSeries (Unit⊕Unit) K)) (Phi.log ()))=
      subst (fun _ : Unit => -(X ():MvPowerSeries Unit K)) (Phi.log ()) := by
    rw [subst_comp_subst_apply FormalGroupLaw.hasSubst_Yemb hp]
    congr 1
    funext s
    rw [subst_X hp]
    rfl
  have h := congrArg (subst (negPair (R:=K))) (Phi.log_subst_F ())
  rw [hleft,subst_add hp,hX,hY] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem short_formal_log_odd {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (h1 : W.a₁=0) (h3 : W.a₃=0) :
    subst (fun _ : Unit => -(X () : MvPowerSeries Unit K)) (W.formalGroupLaw.log ())=
      -W.formalGroupLaw.log () :=
  formal_log_odd W.formalGroupLaw (short_inverse_substitution W h1 h3)

/-- In particular, the quadratic coefficient of the actual short-curve log
vanishes, rather than being discarded as a convenient approximation. -/
theorem short_formal_log_quadratic {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (h1 : W.a₁=0) (h3 : W.a₃=0) :
    coeff (Finsupp.single () 2) (W.formalGroupLaw.log ())=0 := by
  have h := short_formal_log_odd W h1 h3
  have hr : subst (fun _ : Unit => -(X () : MvPowerSeries Unit K)) (W.formalGroupLaw.log ())=
      rescale (fun _ : Unit => (-1:K)) (W.formalGroupLaw.log ()) := by
    rw [rescale_eq_subst]
    congr 1
    funext u
    simp
  rw [hr] at h
  have hc := congrArg (coeff (Finsupp.single () 2)) h
  simp only [coeff_rescale,map_neg,Finsupp.prod_single_index,pow_zero,neg_one_sq,one_mul] at hc
  linear_combination (1/2:K)*hc

#print axioms short_inverse
#print axioms short_formal_log_odd
#print axioms short_formal_log_quadratic
end FourCorner.CommonSource.LogPrecision
