import ChartSectionGeneric
import CriticalSchemeCount

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicCurve MvPolynomial HomogeneousLocalization
universe u
namespace FourCorner.CriticalChartGenericFunctions
open CriticalProj23 CriticalStandardCharts CriticalChartBase CriticalHomogeneousEvaluation
variable {k:Type u} [Field k]

instance chart_nonempty (i:k) (j:Fin 4):Nonempty (Proj.basicOpen (criticalGrading i) (coordinate i j)) := by
  let p:=signedSchemePoint i (fun _=>false)
  have hp:p ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i j)=⊤ := by
    change pointOfCoordinates i _ _ _ ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i j)=⊤
    rw [pointOfCoordinates_preimage_chart]
    fin_cases j <;> simp [CriticalElliptic23.signedVector,CriticalElliptic23.sign]
  refine ⟨⟨p (IsLocalRing.closedPoint k),?_⟩⟩
  change IsLocalRing.closedPoint k∈p ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i j)
  rw [hp];trivial

lemma chartSection_eq_away (i:k) (j:Fin 4) (r:affineRing i j) :
 ChartSectionGeneric.chartSection (Proj.basicOpen (criticalGrading i) (coordinate i j)) (chartIso i j) r=
   Proj.awayToSection (criticalGrading i) (coordinate i j) ((qequiv i j).symm r) := by
  unfold ChartSectionGeneric.chartSection
  change (Proj.basicOpen (criticalGrading i) (coordinate i j)).topIso.hom
   (((Proj.basicOpenToSpec (criticalGrading i) (coordinate i j))≫
    Spec.map (CommRingCat.ofHom (qequiv i j).symm.toRingHom)).appTop
      ((Scheme.ΓSpecIso (.of (affineRing i j))).inv r))=_
  rw [Scheme.Hom.comp_appTop]
  have hn:=Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (qequiv i j).symm.toRingHom)
  have hn':(Spec.map (CommRingCat.ofHom (qequiv i j).symm.toRingHom)).appTop
    ((Scheme.ΓSpecIso (.of (affineRing i j))).inv r)=
    (Scheme.ΓSpecIso (.of (Away (criticalGrading i) (coordinate i j)))).inv ((qequiv i j).symm r) :=
    (congrArg (fun g:CommRingCat.of (affineRing i j)⟶_=>g.hom r) hn).symm
  change (Proj.basicOpen (criticalGrading i) (coordinate i j)).topIso.hom
    ((Proj.basicOpenToSpec (criticalGrading i) (coordinate i j)).appTop
      ((Spec.map (CommRingCat.ofHom (qequiv i j).symm.toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (affineRing i j))).inv r)))=_
  rw [hn']
  change (Proj.basicOpen (criticalGrading i) (coordinate i j)).topIso.hom
    ((Proj.basicOpenToSpec (criticalGrading i) (coordinate i j)).app ⊤
      ((Scheme.ΓSpecIso (.of (Away (criticalGrading i) (coordinate i j)))).inv ((qequiv i j).symm r)))=_
  rw [Proj.basicOpenToSpec_app_top]
  simp only [ConcreteCategory.comp_apply,Iso.inv_hom_id_apply]
  exact congrArg (fun g:Γ(criticalCurve i,Proj.basicOpen (criticalGrading i) (coordinate i j))⟶Γ(criticalCurve i,Proj.basicOpen (criticalGrading i) (coordinate i j))=>g.hom _)
    (Iso.inv_hom_id (Proj.basicOpen (criticalGrading i) (coordinate i j)).topIso)

lemma qequiv_symm_coordinate (i:k) (j a:Fin 4) :
 (qequiv i j).symm (affineEvaluation i j (X a))=
 Away.mk (criticalGrading i) (coordinate_degree_one i j) 1 (coordinate i a)
  (by simpa only [one_smul] using coordinate_degree_one i a) := by
  apply (qequiv i j).injective
  rw [RingEquiv.apply_symm_apply]
  symm
  exact CriticalQuotientChart.chartDehom_mk (CriticalProj23.equation i) (equation_homogeneous i) j 1 _ _

variable (i:k) [IsIntegral (criticalCurve i)]

def genericMap (j:Fin 4):affineRing i j→+*(criticalCurve i).functionField :=
 ChartSectionGeneric.genericMap (Proj.basicOpen (criticalGrading i) (coordinate i j)) (chartIso i j)

lemma genericMap_stalk (j a:Fin 4) :
 Proj.stalkIso' (criticalGrading i) (genericPoint (criticalCurve i))
   (genericMap i j (affineEvaluation i j (X a)))=
 HomogeneousLocalization.mapId (criticalGrading i)
   (Submonoid.powers_le.mpr (show coordinate i j∉(genericPoint (criticalCurve i)).asHomogeneousIdeal from
     (((genericPoint_spec (criticalCurve i)).mem_open_set_iff
       (Proj.basicOpen (criticalGrading i) (coordinate i j)).isOpen).mpr (by simpa using chart_nonempty i j))))
   (Away.mk (criticalGrading i) (coordinate_degree_one i j) 1 (coordinate i a)
    (by simpa only [one_smul] using coordinate_degree_one i a)) := by
  change Proj.stalkIso' _ _ ((criticalCurve i).germToFunctionField _
    (ChartSectionGeneric.chartSection _ _ _))=_
  rw [chartSection_eq_away,qequiv_symm_coordinate]
  erw [Proj.stalkIso'_germ]
  rfl

lemma genericCoordinate_mul (j l a:Fin 4) :
 genericMap i j (affineEvaluation i j (X a))*genericMap i l (affineEvaluation i l (X j))=
 genericMap i l (affineEvaluation i l (X a)) := by
  apply (Proj.stalkIso' (criticalGrading i) (genericPoint (criticalCurve i))).injective
  rw [map_mul,genericMap_stalk,genericMap_stalk,genericMap_stalk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,HomogeneousLocalization.mapId,
    HomogeneousLocalization.Away.mk,HomogeneousLocalization.map_mk,HomogeneousLocalization.val_mk]
  change Localization.mk (coordinate i a) _ * Localization.mk (coordinate i j) _=
    Localization.mk (coordinate i a) _
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,Submonoid.coe_mul,pow_one]
  change coordinate i l*(coordinate i a*coordinate i j)=coordinate i j*coordinate i l*coordinate i a
  ring

lemma genericCoordinate_self (j:Fin 4):genericMap i j (affineEvaluation i j (X j))=1 := by
  rw [affineEvaluation_X,if_pos rfl,map_one]

#print axioms genericMap_stalk
#print axioms genericCoordinate_mul
end FourCorner.CriticalChartGenericFunctions
