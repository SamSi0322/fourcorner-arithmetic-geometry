import CriticalAllPointResiduePresentation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry AlgebraicCurve MvPolynomial
universe u
namespace FourCorner.CriticalLiteralSchemeCharacter
open CriticalProj23 CriticalStandardCharts CriticalSchemePointPlaces CriticalChartResidueEvaluation
variable {k:Type u} [Field k]

/-- EVERY actual original point is reconstructed from its residue vector,
whose positive-degree homogeneous polynomial opens are the literal original
coordinate evaluations. No unrelated point or raw tuple replaces that point. -/
theorem same_point_homogeneous (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (P:BasePoints i)
 (p:Ambient k) {d:ℕ} (hp:p.IsHomogeneous d) (hd:0<d) :
 P.val ⁻¹ᵁ Proj.basicOpen (criticalGrading i) ((CriticalChartBase.qmap i) p)=
 PrimeSpectrum.basicOpen (MvPolynomial.eval (CriticalSchemeCount.residueVector i hi h2 P) p) := by
  obtain ⟨j,hj,hv,he⟩:=CriticalAllPointResiduePresentation.same_point_normalized i hi h2 P
  have h:=CriticalNormalizedChartPoint.point_preimage_homogeneous i j
    (CriticalSchemeCount.residueVector i hi h2 P)
    (CriticalProjectiveResidues.vector_critical i hi h2 (baseEquiv i hi h2 P).val (baseEquiv i hi h2 P).property)
    hv p hp hd
  exact (congrArg (fun q:BasePoints i=>q.val ⁻¹ᵁ Proj.basicOpen (criticalGrading i) ((CriticalChartBase.qmap i) p)) he).trans h

variable [Fintype k] [DecidableEq k]
/-- The existing scheme count character is the literal paper character in
an exact native coordinate presentation of the SAME actual Scheme point. -/
theorem literal_character (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (P:BasePoints i) :
 ∃(j:Fin 4) (f:affineRing i j→ₐ[k]k), (j=0 ∨j=1) ∧affinePoint i j f=P ∧
 let v:=CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a))
 CriticalSchemeCount.residueVector i hi h2 P=v ∧
 CriticalSchemeCount.character i hi h2 P=quadraticChar k (2*(v 0*v 3+v 1*v 2)) := by
  obtain ⟨j,f,hj,hf,hv⟩:=CriticalAllPointResiduePresentation.same_point_chart i hi h2 P
  refine ⟨j,f,hj,hf,hv,?_⟩
  unfold CriticalSchemeCount.character
  rw [hv]
  rfl

#print axioms same_point_homogeneous
#print axioms literal_character
end FourCorner.CriticalLiteralSchemeCharacter
