import CriticalNormalizedChartPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicCurve MvPolynomial
universe u
namespace FourCorner.CriticalAllPointResiduePresentation
open CriticalProj23 CriticalStandardCharts CriticalChartBase CriticalHomogeneousEvaluation CriticalRadicalField
open CriticalSchemePointPlaces CriticalProjectiveResidues ResiduePlaceEvaluation CriticalChartResidueEvaluation
variable {k:Type u} [Field k]
local instance baseConstants (i:k):Algebra k (CriticalLiteralDouble.base k i):=CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k):Module k (CriticalLiteralDouble.base k i):=(baseConstants i).toModule

lemma factors_chart (i:k) (p:BasePoints i) (j:Fin 4)
 (hp:p.val (IsLocalRing.closedPoint k)∈Proj.basicOpen (criticalGrading i) (coordinate i j)) :
 ∃f:affineRing i j→ₐ[k]k,affinePoint i j f=p := by
  let U:=Proj.basicOpen (criticalGrading i) (coordinate i j)
  have hr:Set.range p.val⊆Set.range U.ι := by
    rintro _ ⟨x,rfl⟩
    refine ⟨⟨p.val x,?_⟩,rfl⟩
    simpa only [Subsingleton.elim x (IsLocalRing.closedPoint k)] using hp
  let q:=IsOpenImmersion.lift U.ι p.val hr
  have hq:q≫U.ι=p.val:=IsOpenImmersion.lift_fac U.ι p.val hr
  obtain ⟨f,hf⟩:=CriticalExtensionPoints.algebra_of_chart_factor i p.val
    (by simpa only [Algebra.algebraMap_self,CommRingCat.ofHom_id,Spec.map_id] using p.property) j q hq
  exact ⟨f,Subtype.ext hf⟩

lemma zero_or_one (i:k) (p:BasePoints i) :
 p.val (IsLocalRing.closedPoint k)∈Proj.basicOpen (criticalGrading i) (coordinate i 0) ∨
 p.val (IsLocalRing.closedPoint k)∈Proj.basicOpen (criticalGrading i) (coordinate i 1) := by
  have h:=CriticalTwoChartCover.two_charts_cover i
  have hm:p.val (IsLocalRing.closedPoint k)∈
    Proj.basicOpen (criticalGrading i) (coordinate i 0)⊔Proj.basicOpen (criticalGrading i) (coordinate i 1) := by
    rw [h];trivial
  exact hm

lemma finite_factors (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (p:BasePoints i)
 (ha:0≤(baseEquiv i hi h2 p).val.ord (a k i)) :
 ∃f:affineRing i 0→ₐ[k]k,affinePoint i 0 f=p := by
  by_cases h0:p.val (IsLocalRing.closedPoint k)∈Proj.basicOpen (criticalGrading i) (coordinate i 0)
  · exact factors_chart i p 0 h0
  obtain ⟨f,hf⟩:=factors_chart i p 1 ((zero_or_one i p).resolve_left h0)
  subst p
  let w:=baseEquiv i hi h2 (affinePoint i 1 f)
  obtain ⟨A,B,C,hA,hB,hC,heA,heB,heC⟩:=pole_coordinates i hi h2 f
  have hn:(A:CriticalLiteralDouble.base k i)≠0:=by rw [hA];exact inv_ne_zero (CriticalBadUnits.ordered_nonzero i hi h2).1
  have hm:=((w.val.mem_iff_ord_nonneg hn).mp A.property)
  rw [hA,ord_inverse] at hm
  change 0≤w.val.ord (a k i) at ha
  have hz:w.val.ord (A:CriticalLiteralDouble.base k i)=0:=by rw [hA,ord_inverse];omega
  have he:=ResidueValuationFacts.evaluate_nonzero_of_ord_zero w.val w.property A hn hz
  rw [heA] at he
  have ht:=point_preimage i 1 f (X (0:Fin 4)) (isHomogeneous_X k 0) one_pos
  change _ ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i 0)=_ at ht
  have htop:PrimeSpectrum.basicOpen (f (affineEvaluation i 1 (X 0)))=⊤:=by
    apply top_le_iff.mp
    intro x _
    exact Ideal.notMem_of_isUnit x.asIdeal (isUnit_iff_ne_zero.mpr he)
  have hx:(affinePoint i 1 f).val (IsLocalRing.closedPoint k)∈
     Proj.basicOpen (criticalGrading i) (coordinate i 0) := by
    change IsLocalRing.closedPoint k∈(affinePoint i 1 f).val ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i 0)
    rw [show (affinePoint i 1 f).val ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i 0)=⊤ from ht.trans htop]
    trivial
  exact (h0 hx).elim

lemma pole_factors (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (p:BasePoints i)
 (ha:(baseEquiv i hi h2 p).val.ord (a k i)<0) :
 ∃f:affineRing i 1→ₐ[k]k,affinePoint i 1 f=p := by
  rcases zero_or_one i p with h0|h1
  · obtain ⟨f,hf⟩:=factors_chart i p 0 h0
    have hn:=finite_nonnegative i hi h2 f
    rw [hf] at hn
    omega
  · exact factors_chart i p 1 h1

/-- EVERY original Scheme point has a SAME-point original native chart
presentation with EXACTLY its normalized original-field residue vector. -/
theorem same_point_chart (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (p:BasePoints i) :
 ∃(j:Fin 4) (f:affineRing i j→ₐ[k]k), (j=0 ∨j=1) ∧affinePoint i j f=p ∧
 CriticalSchemeCount.residueVector i hi h2 p=CriticalChartSmooth.normalizedVector j
   (fun a=>f (CriticalChartJacobian.ax i j a)) := by
  by_cases ha:0≤(baseEquiv i hi h2 p).val.ord (a k i)
  · obtain ⟨f,hf⟩:=finite_factors i hi h2 p ha
    refine ⟨0,f,Or.inl rfl,hf,?_⟩
    rw [←hf]
    exact finite_vector i hi h2 f
  · have hn:(baseEquiv i hi h2 p).val.ord (a k i)<0:=by omega
    obtain ⟨f,hf⟩:=pole_factors i hi h2 p hn
    refine ⟨1,f,Or.inr rfl,hf,?_⟩
    rw [←hf] at hn ⊢
    exact pole_vector i hi h2 f hn

/-- The canonical literal normalized native-chart constructor returns the
SAME original Scheme point, including every original V0 pole. -/
theorem same_point_normalized (i:k) (hi:i^2= -1) (h2:(2:k)≠0) (p:BasePoints i) :
 ∃(j:Fin 4) (hj:j=0 ∨j=1) (hv:CriticalSchemeCount.residueVector i hi h2 p j=1),
 p=CriticalNormalizedChartPoint.point i j (CriticalSchemeCount.residueVector i hi h2 p)
   (CriticalProjectiveResidues.vector_critical i hi h2 (baseEquiv i hi h2 p).val (baseEquiv i hi h2 p).property) hv := by
  obtain ⟨j,f,hj,hf,hv⟩:=same_point_chart i hi h2 p
  have hjv:CriticalSchemeCount.residueVector i hi h2 p j=1:=by
    rw [hv,CriticalChartSmooth.normalizedVector_self]
  refine ⟨j,hj,hjv,?_⟩
  calc
    p=affinePoint i j f:=hf.symm
    _=CriticalNormalizedChartPoint.point i j (CriticalSchemeCount.residueVector i hi h2 p) _ hjv:=
      congrArg (affinePoint i j) (CriticalNormalizedChartPoint.chartEvaluation_unique i j f _ _ _ hv.symm)

#print axioms same_point_chart
#print axioms same_point_normalized
end FourCorner.CriticalAllPointResiduePresentation
