import CriticalBoundaryChart
import CriticalAffineTower

noncomputable section
namespace FourCorner.CriticalSignPoints
open AlgebraicGeometry CategoryTheory
open CriticalProj23 CriticalStandardCharts CriticalElliptic23 CriticalHomogeneousEvaluation
variable {k : Type*} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def zeroAlgEquiv (i : k) : affineRing i 0 ≃ₐ[k] CriticalAffineGeometry.ring i :=
  Ideal.quotientEquivAlgOfEq k (zero_ideal i)

lemma zeroAlgEquiv_ax (i : k) (a : Fin 3) :
    zeroAlgEquiv i (CriticalChartJacobian.ax i 0 a)=CriticalAffineGeometry.coordinate i a := by
  rfl

lemma sign_sq (e : Bool) : (sign (k:=k) e)^2=1 := by cases e <;> simp [sign]

def literalEvaluation (i : k) (e : Fin 3 → Bool) : CriticalAffineGeometry.ring i →ₐ[k] k :=
  CriticalAffineGeometry.ofCoordinates i (sign (e 0)) (sign (e 1)) (sign (e 2))
    (by simp only [sign_sq,sub_self,mul_zero]) (by simp only [sign_sq,sub_self,mul_zero])

def evaluation (i : k) (e : Fin 3 → Bool) : affineRing i 0 →ₐ[k] k :=
  (literalEvaluation i e).comp (zeroAlgEquiv i).toAlgHom

@[simp] lemma evaluation_ax (i : k) (e : Fin 3 → Bool) (a : Fin 3) :
    evaluation i e (CriticalChartJacobian.ax i 0 a)=sign (e a) := by
  rw [evaluation,AlgHom.comp_apply]
  change literalEvaluation i e (zeroAlgEquiv i (CriticalChartJacobian.ax i 0 a))=_
  rw [zeroAlgEquiv_ax]
  change CriticalAffineGeometry.ofCoordinates i _ _ _ _ _ (CriticalAffineGeometry.coordinate i a)=_
  rw [CriticalAffineGeometry.ofCoordinates_coordinate]
  fin_cases a <;> rfl

/-- The eight displayed actual projective points, defined in their literal
normalized V0 chart, hence retaining [1:eps1:eps2:eps3] as actual coordinates. -/
def point (i : k) (e : Fin 3 → Bool) : Spec (.of k) ⟶ criticalCurve i :=
  Spec.map (CommRingCat.ofHom (evaluation i e).toRingHom) ≫ (chartIso i 0).inv ≫
    (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι

lemma point_over (i : k) (e : Fin 3 → Bool) : point i e ≫ criticalToSpec i=𝟙 _ := by
  simp only [point,Category.assoc]
  rw [CriticalChartBase.chart_over_base,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((evaluation i e).toRingHom.comp (algebraMap k (affineRing i 0))))=𝟙 _
  have hc : (evaluation i e).toRingHom.comp (algebraMap k (affineRing i 0))=RingHom.id k := by
    ext a;exact (evaluation i e).commutes a
  rw [hc]
  simp only [CommRingCat.ofHom_id,Spec.map_id]
end FourCorner.CriticalSignPoints
#print axioms FourCorner.CriticalSignPoints.point_over
#print axioms FourCorner.CriticalSignPoints.evaluation_ax
