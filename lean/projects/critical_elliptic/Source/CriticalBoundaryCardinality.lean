import CriticalSignPoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u
namespace FourCorner.CriticalBoundaryCardinality
open CriticalProj23 CriticalStandardCharts CriticalElliptic23 CriticalSignPoints
variable {k L : Type u} [Field k] [Field L] [Algebra k L]

def pointOver (i : k) (e : Fin 3 → Bool) : Spec (.of L) ⟶ criticalCurve i :=
  Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ point i e

/-- The eight actual Scheme points remain distinct after EVERY extension of
constants, by faithfulness on their literal normalized coordinate maps. -/
theorem pointOver_injective (i : k) (h2 : (2:k)≠0) :
    Function.Injective (pointOver (L:=L) i) := by
  intro e d h
  have h' :
      (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫
        Spec.map (CommRingCat.ofHom (evaluation i e).toRingHom)) ≫
          ((chartIso i 0).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι) =
      (Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫
        Spec.map (CommRingCat.ofHom (evaluation i d).toRingHom)) ≫
          ((chartIso i 0).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι) := by
    simpa only [pointOver,point,Category.assoc] using h
  have he := (cancel_mono ((chartIso i 0).inv ≫
    (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι)).mp h'
  rw [←Spec.map_comp,←Spec.map_comp] at he
  have hr := congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  funext a
  apply sign_injective h2
  apply (algebraMap k L).injective
  have hv := RingHom.congr_fun hr (CriticalChartJacobian.ax i 0 a)
  change algebraMap k L (evaluation i e (CriticalChartJacobian.ax i 0 a)) =
    algebraMap k L (evaluation i d (CriticalChartJacobian.ax i 0 a)) at hv
  simpa only [evaluation_ax] using hv

theorem point_injective (i : k) (h2 : (2:k)≠0) : Function.Injective (point i) := by
  intro e d h
  apply pointOver_injective (L:=k) i h2
  simpa only [pointOver,Algebra.algebraMap_self,CommRingCat.ofHom_id,Spec.map_id,
    Category.id_comp] using h

theorem pointOver_card (i : k) (h2 : (2:k)≠0) :
    Nat.card (Set.range (pointOver (L:=L) i)) = 8 := by
  rw [← Nat.card_congr (Equiv.ofInjective (pointOver (L:=L) i) (pointOver_injective i h2))]
  simp

theorem point_card (i : k) (h2 : (2:k)≠0) : Nat.card (Set.range (point i)) = 8 := by
  rw [← Nat.card_congr (Equiv.ofInjective (point i) (point_injective i h2))]
  simp

end FourCorner.CriticalBoundaryCardinality
#print axioms FourCorner.CriticalBoundaryCardinality.pointOver_injective
#print axioms FourCorner.CriticalBoundaryCardinality.point_injective
#print axioms FourCorner.CriticalBoundaryCardinality.pointOver_card
#print axioms FourCorner.CriticalBoundaryCardinality.point_card
