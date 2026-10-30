import CriticalHomogeneousEvaluation

noncomputable section
namespace FourCorner.CriticalBoundaryChart
open AlgebraicGeometry CategoryTheory MvPolynomial
open CriticalProj23 CriticalStandardCharts CriticalChartBase CriticalHomogeneousEvaluation
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

lemma boundary_shift_zero (i : k) (j : Fin 4) (f : affineRing i j →ₐ[k] L)
    (hb : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso i j).inv ≫
      (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι) ⁻¹ᵁ shiftOpen i=⊥) :
    CriticalElliptic23.Shift (CriticalChartSmooth.normalizedVector j
      (fun a=>f (CriticalChartJacobian.ax i j a)))=0 := by
  have hpre:=point_preimage i j f (shiftPolynomial (k:=k)) shift_homogeneous (by decide : 0<2)
  change _=PrimeSpectrum.basicOpen (f (affineEvaluation i j (shiftPolynomial (k:=k)))) at hpre
  have hz : PrimeSpectrum.basicOpen (f (affineEvaluation i j (shiftPolynomial (k:=k))))=⊥ := hpre.symm.trans hb
  have he := isNilpotent_iff_eq_zero.mp ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp hz)
  rw [shift_value] at he
  exact he

/-- EVERY field-valued boundary point of original Ci(k) lies in its V0 chart.
The extension-field structure map is retained, not replaced by a k-point count. -/
theorem factors_zero_chart (i : k) (p : Spec (.of L) ⟶ criticalCurve i)
    (hp : p ≫ criticalToSpec i=Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hb : p ⁻¹ᵁ shiftOpen i=⊥) :
    ∃ f : affineRing i 0 →ₐ[k] L,
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso i 0).inv ≫
        (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι=p ∧
      CriticalElliptic23.Shift (CriticalChartSmooth.normalizedVector 0
        (fun a=>f (CriticalChartJacobian.ax i 0 a)))=0 := by
  obtain ⟨j,f,hf,hc,hj⟩:=CriticalExtensionPoints.point_coordinates i p hp
  have hs:=boundary_shift_zero i j f (by rw [hf];exact hb)
  have hv0 := CriticalElliptic23.boundary_zero_nonzero (algebraMap k L i) _ hc hs
    ⟨j,by rw [hj];exact one_ne_zero⟩
  have hpre:=point_preimage i j f (X (0:Fin 4)) (isHomogeneous_X k 0) one_pos
  have hU : p ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i 0)=⊤ := by
    rw [←hf]
    change _ ⁻¹ᵁ Proj.basicOpen (criticalGrading i) ((qmap i) (X 0))=_
    rw [hpre,coordinate_value]
    have he:=PrimeSpectrum.basicOpen_mul (CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a)) 0) ((CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a)) 0)⁻¹)
    rw [mul_inv_cancel₀ hv0,PrimeSpectrum.basicOpen_one] at he
    exact top_le_iff.mp (he.trans_le inf_le_left)
  let U:=Proj.basicOpen (criticalGrading i) (coordinate i 0)
  have hr : Set.range p⊆Set.range U.ι := by
    rintro y ⟨x,rfl⟩
    refine ⟨⟨p x,?_⟩,rfl⟩
    change x∈p ⁻¹ᵁ U
    rw [hU]
    trivial
  let q:=IsOpenImmersion.lift U.ι p hr
  have hq : q ≫ U.ι=p:=IsOpenImmersion.lift_fac U.ι p hr
  obtain ⟨g,hg⟩:=CriticalExtensionPoints.algebra_of_chart_factor i p hp 0 q hq
  exact ⟨g,hg,boundary_shift_zero i 0 g (by rw [hg];exact hb)⟩
end FourCorner.CriticalBoundaryChart
#print axioms FourCorner.CriticalBoundaryChart.factors_zero_chart
