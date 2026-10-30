import CriticalSignPoints

noncomputable section
namespace FourCorner.CriticalBoundaryClassification
open AlgebraicGeometry CategoryTheory MvPolynomial
open CriticalProj23 CriticalStandardCharts CriticalHomogeneousEvaluation CriticalSignPoints CriticalElliptic23
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

lemma chart_hom_ext (i : k) (j : Fin 4) (f g : affineRing i j →ₐ[k] L)
    (h : ∀ a,f (CriticalChartJacobian.ax i j a)=g (CriticalChartJacobian.ax i j a)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact (f.commutes a).trans (g.commutes a).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p a hp => simpa only [map_mul,CriticalChartJacobian.ax] using congrArg₂ (·*·) hp (h a)

lemma point_boundary (i : k) (e : Fin 3 → Bool) : point i e ⁻¹ᵁ shiftOpen i=⊥ := by
  have h:=point_preimage i 0 (evaluation i e) (shiftPolynomial (k:=k)) shift_homogeneous (by decide : 0<2)
  have hz : evaluation i e (affineEvaluation i 0 (shiftPolynomial (k:=k)))=0 := by
    rw [shift_value]
    change evaluation i e (CriticalChartJacobian.ax i 0 0)^2-(1:k)^2=0
    rw [evaluation_ax,sign_sq]
    ring
  rw [hz,PrimeSpectrum.basicOpen_zero] at h
  exact h

/-- Complete geometric boundary classification on the ORIGINAL projective
scheme. It covers arbitrary field-valued points and proves exact equality to
one of the eight k-defined sign points after that field extension. -/
theorem geometric_boundary (i : k) (p : Spec (.of L) ⟶ criticalCurve i)
    (hp : p ≫ criticalToSpec i=Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    p ⁻¹ᵁ shiftOpen i=⊥ ↔ ∃ e : Fin 3 → Bool,
      p=Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ point i e := by
  constructor
  · intro hb
    obtain ⟨f,hf,hs⟩:=CriticalBoundaryChart.factors_zero_chart i p hp hb
    have hc:=CriticalChartSmooth.field_point_coordinates i 0 L f
    change (f (CriticalChartJacobian.ax i 0 1)^2-(1:L)^2=algebraMap k L i*(f (CriticalChartJacobian.ax i 0 0)^2-(1:L)^2)) ∧
      (f (CriticalChartJacobian.ax i 0 2)^2-(1:L)^2=(1+algebraMap k L i)*(f (CriticalChartJacobian.ax i 0 0)^2-(1:L)^2)) at hc
    simp only [one_pow] at hc
    change f (CriticalChartJacobian.ax i 0 0)^2-(1:L)^2=0 at hs
    have ha : f (CriticalChartJacobian.ax i 0 0)^2=1 := by linear_combination hs
    have hsq : ∀ a : Fin 3,f (CriticalChartJacobian.ax i 0 a)^2=1 := by
      intro a
      fin_cases a
      · exact ha
      · change f (CriticalChartJacobian.ax i 0 1)^2=1
        linear_combination hc.1+(algebraMap k L i)*hs
      · change f (CriticalChartJacobian.ax i 0 2)^2=1
        linear_combination hc.2+(1+algebraMap k L i)*hs
    have hsign : ∀ a : Fin 3,∃ b : Bool,
        f (CriticalChartJacobian.ax i 0 a)=algebraMap k L (sign (k:=k) b) := by
      intro a
      have hh : f (CriticalChartJacobian.ax i 0 a)^2=(1:L)^2 := by simpa only [one_pow] using hsq a
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h|h
      · exact ⟨false,by simpa only [sign,Bool.false_eq_true,ite_false,map_one] using h⟩
      · exact ⟨true,by simpa only [sign,ite_true,map_neg,map_one] using h⟩
    let e : Fin 3 → Bool:=fun a=>Classical.choose (hsign a)
    have he (a : Fin 3) : f (CriticalChartJacobian.ax i 0 a)=algebraMap k L (sign (k:=k) (e a)) :=
      Classical.choose_spec (hsign a)
    let g : affineRing i 0 →ₐ[k] L := (Algebra.ofId k L).comp (evaluation i e)
    have hfg : f=g := by
      apply chart_hom_ext
      intro a
      change f (CriticalChartJacobian.ax i 0 a)=algebraMap k L (evaluation i e (CriticalChartJacobian.ax i 0 a))
      rw [evaluation_ax]
      exact he a
    refine ⟨e,?_⟩
    rw [←hf,hfg]
    change Spec.map (CommRingCat.ofHom ((algebraMap k L).comp (evaluation i e).toRingHom)) ≫
      (chartIso i 0).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι=_
    rw [CommRingCat.ofHom_comp,Spec.map_comp]
    simp only [Category.assoc,point]
  · rintro ⟨e,rfl⟩
    rw [Scheme.Hom.comp_preimage,point_boundary]
    rfl
end FourCorner.CriticalBoundaryClassification
#print axioms FourCorner.CriticalBoundaryClassification.geometric_boundary
#print axioms FourCorner.CriticalBoundaryClassification.point_boundary
