import CriticalFixedChartCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicCurve MvPolynomial
universe u
namespace FourCorner.CriticalChartResidueEvaluation
open CriticalProj23 CriticalStandardCharts CriticalChartBase CriticalHomogeneousEvaluation CriticalRadicalField
open CriticalSchemePointPlaces CriticalProjectiveResidues ResiduePlaceEvaluation
variable {k:Type u} [Field k]
local instance baseConstants (i:k):Algebra k (CriticalLiteralDouble.base k i):=CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k):Module k (CriticalLiteralDouble.base k i):=(baseConstants i).toModule

def affinePoint (i:k) (j:Fin 4) (f:affineRing i j→ₐ[k]k):BasePoints i :=
 ⟨Spec.map (CommRingCat.ofHom f.toRingHom)≫(chartIso i j).inv≫
   (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι,by
  simp only [Category.assoc]
  rw [chart_over_base,←Spec.map_comp,←CommRingCat.ofHom_comp]
  have h:f.toRingHom.comp (algebraMap k (affineRing i j))=RingHom.id k:=by ext x;exact f.commutes x
  rw [h,CommRingCat.ofHom_id,Spec.map_id]⟩

theorem evaluate_at (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (j:Fin 4)
 (f:affineRing i j→ₐ[k]k) (x:CriticalLiteralDouble.base k i) (r:affineRing i j) :
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=SmoothCurveExtension.fieldAlgebra (criticalToSpec i)
 CriticalDoubleOriginalMap.baseFieldEquiv i hi h2 x=CriticalChartGenericFunctions.genericMap i j r →
 let w:=baseEquiv i hi h2 (affinePoint i j f)
 ∃b:w.val.toValuationSubring,(b:CriticalLiteralDouble.base k i)=x ∧evaluate w.val w.property b=f r := by
  letI:=CriticalProjectiveIntegral.projective_integral i hi h2
  letI : IsIntegral (Proj (criticalGrading i)):=CriticalProjectiveIntegral.projective_integral i hi h2
  letI:=CriticalProjectiveSmooth.projective_smooth i hi h2
  letI:=CriticalProj23.criticalToSpec_isProper i
  letI:=SmoothCurveExtension.fieldAlgebra (criticalToSpec i)
  intro hx
  have h:=ChartSectionGeneric.fixed_chart_evaluate (criticalToSpec i)
    (Proj.basicOpen (criticalGrading i) (coordinate i j)) (chartIso i j)
    (chart_over_base i j) f x r (CriticalDoubleOriginalMap.baseFieldEquiv i hi h2) hx
  exact h

theorem finite_coordinates (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (f:affineRing i 0→ₐ[k]k) :
 let w:=baseEquiv i hi h2 (affinePoint i 0 f)
 ∃A B C:w.val.toValuationSubring,
 (A:CriticalLiteralDouble.base k i)=a k i ∧(B:CriticalLiteralDouble.base k i)=b k i ∧
 (C:CriticalLiteralDouble.base k i)=c k i ∧
 evaluate w.val w.property A=f (affineEvaluation i 0 (X 1)) ∧
 evaluate w.val w.property B=f (affineEvaluation i 0 (X 2)) ∧
 evaluate w.val w.property C=f (affineEvaluation i 0 (X 3)) := by
  have hc:=CriticalFixedChartCoordinates.base_coordinates i hi h2
  obtain ⟨A,hA,heA⟩:=evaluate_at i hi h2 0 f _ _ hc.1
  obtain ⟨B,hB,heB⟩:=evaluate_at i hi h2 0 f _ _ hc.2.1
  obtain ⟨C,hC,heC⟩:=evaluate_at i hi h2 0 f _ _ hc.2.2
  exact ⟨A,B,C,hA,hB,hC,heA,heB,heC⟩

theorem pole_coordinates (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (f:affineRing i 1→ₐ[k]k) :
 let w:=baseEquiv i hi h2 (affinePoint i 1 f)
 ∃A B C:w.val.toValuationSubring,
 (A:CriticalLiteralDouble.base k i)=(a k i)⁻¹ ∧(B:CriticalLiteralDouble.base k i)=b k i/a k i ∧
 (C:CriticalLiteralDouble.base k i)=c k i/a k i ∧
 evaluate w.val w.property A=f (affineEvaluation i 1 (X 0)) ∧
 evaluate w.val w.property B=f (affineEvaluation i 1 (X 2)) ∧
 evaluate w.val w.property C=f (affineEvaluation i 1 (X 3)) := by
  have hc:=CriticalFixedChartCoordinates.pole_coordinates i hi h2
  obtain ⟨A,hA,heA⟩:=evaluate_at i hi h2 1 f _ _ hc.1
  obtain ⟨B,hB,heB⟩:=evaluate_at i hi h2 1 f _ _ hc.2.1
  obtain ⟨C,hC,heC⟩:=evaluate_at i hi h2 1 f _ _ hc.2.2
  exact ⟨A,B,C,hA,hB,hC,heA,heB,heC⟩

theorem finite_nonnegative (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (f:affineRing i 0→ₐ[k]k) :
 0≤(baseEquiv i hi h2 (affinePoint i 0 f)).val.ord (a k i) := by
  obtain ⟨A,B,C,hA,hB,hC,heA,heB,heC⟩:=finite_coordinates i hi h2 f
  have hm:=A.property
  rw [hA] at hm
  exact ((baseEquiv i hi h2 (affinePoint i 0 f)).val.mem_iff_ord_nonneg
    (CriticalBadUnits.ordered_nonzero i hi h2).1).mp hm

theorem finite_vector (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (f:affineRing i 0→ₐ[k]k) :
 let w:=baseEquiv i hi h2 (affinePoint i 0 f)
 vector i hi h2 w.val w.property=CriticalChartSmooth.normalizedVector 0
   (fun j=>f (CriticalChartJacobian.ax i 0 j)) := by
  let w:=baseEquiv i hi h2 (affinePoint i 0 f)
  have hn:=finite_nonnegative i hi h2 f
  obtain ⟨A,B,C,hA,hB,hC,heA,heB,heC⟩:=finite_coordinates i hi h2 f
  have hA':regularA i hi h2 w.val hn=A:=Subtype.ext hA.symm
  have hB':regularB i hi h2 w.val hn=B:=Subtype.ext hB.symm
  have hC':regularC i hi h2 w.val hn=C:=Subtype.ext hC.symm
  change CriticalProjectiveResidues.vector i hi h2 w.val w.property=_
  unfold CriticalProjectiveResidues.vector
  rw [dif_pos hn,CriticalProjectiveResidues.finiteVector,hA',hB',hC',heA,heB,heC]
  funext j
  fin_cases j <;> simp [CriticalChartSmooth.normalizedVector,affineEvaluation_X,CriticalAmbientChart.drop]

theorem pole_vector (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (f:affineRing i 1→ₐ[k]k)
 (hn:(baseEquiv i hi h2 (affinePoint i 1 f)).val.ord (a k i)<0) :
 let w:=baseEquiv i hi h2 (affinePoint i 1 f)
 vector i hi h2 w.val w.property=CriticalChartSmooth.normalizedVector 1
   (fun j=>f (CriticalChartJacobian.ax i 1 j)) := by
  let w:=baseEquiv i hi h2 (affinePoint i 1 f)
  obtain ⟨A,B,C,hA,hB,hC,heA,heB,heC⟩:=pole_coordinates i hi h2 f
  have hA':poleZero i hi h2 w.val hn=A:=Subtype.ext hA.symm
  have hB':poleB i hi h2 w.val hn=B:=Subtype.ext hB.symm
  have hC':poleC i hi h2 w.val hn=C:=Subtype.ext hC.symm
  change CriticalProjectiveResidues.vector i hi h2 w.val w.property=_
  unfold CriticalProjectiveResidues.vector
  rw [dif_neg (not_le.mpr (show w.val.ord (a k i)<0 from hn)),CriticalProjectiveResidues.poleVector,hA',hB',hC',heA,heB,heC]
  funext j
  fin_cases j <;> simp [CriticalChartSmooth.normalizedVector,affineEvaluation_X,CriticalAmbientChart.drop]

#print axioms evaluate_at
#print axioms finite_vector
#print axioms pole_vector
end FourCorner.CriticalChartResidueEvaluation
