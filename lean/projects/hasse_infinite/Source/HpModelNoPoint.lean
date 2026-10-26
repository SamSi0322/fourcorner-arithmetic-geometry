import HpSchemeModel
import HpFamilyNoPoint
import HpResidueCharts
import CurveRationalPlace07

namespace FourCorner.HpModelNoPoint
open AlgebraicCurve AlgebraicGeometry CategoryTheory HpResidueCharts
noncomputable section
local instance constantAlgebra (p : ℚ) : Algebra ℚ (HpSchemeModel.field p) :=
  HpSchemeModel.modelFieldAlgebra p
local instance constantModule (p : ℚ) : Module ℚ (HpSchemeModel.field p) := Algebra.toModule

theorem finite_source {K : Type*} [Field K] [CharZero K] (p a : K) (r : Fin 4 → K)
    (hr : ∀i,r i^2=values p a i) : CompleteSource11.Source p 1 (r 0) (r 1) (r 2) (r 3) := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  change r 0^2=p*a at h0
  change r 1^2=2*(p-1)*(a-1) at h1
  change r 2^2=2*(p+1)*(a+1) at h2
  change r 3^2=(p-1)*a+p+1 at h3
  unfold CompleteSource11.Source
  constructor
  · rw [h1,h0];ring
  constructor
  · rw [h2,h0];ring
  · rw [h3,h0];ring

theorem infinity_source {K : Type*} [Field K] [CharZero K] (p : K) (hp : p ≠ 0)
    (r : Fin 3 → K) (hr : ∀i,r i^2=infinityValues p p⁻¹ 0 i) :
    CompleteSource11.Source p 0 1 (r 0) (r 1) (r 2) := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  simp only [infinityValues,mul_zero,add_zero,sub_zero,add_zero] at h0 h1 h2
  unfold CompleteSource11.Source
  constructor
  · rw [h0];field_simp [hp];ring
  constructor
  · rw [h1];field_simp [hp];ring
  · rw [h2];field_simp [hp];ring

/-- Every rational place of the actual literal function field produces an
original homogeneous source, including all finite branch and infinity cases. -/
theorem rational_place_source (p : ℚ) (hp : p ≠ 0)
    (w : Place ℚ (HpLiteralField.field ℚ p)) (hw : w.IsRational) :
    Nonempty (HasseRationalSource.HomogeneousPoint p) := by
  rcases exhaustive_charts ℚ p hp w hw with ⟨a,r,hr⟩ | ⟨r,hr⟩
  · exact ⟨⟨1,r 0,r 1,r 2,r 3,by simp,finite_source p a r hr⟩⟩
  · exact ⟨⟨0,1,r 0,r 1,r 2,by simp,infinity_source p hp r hr⟩⟩

theorem family_no_rational_place (j : ℕ) :
    ¬ ∃w : Place ℚ (HpSchemeModel.field (HpInfiniteArithmetic.p j)),w.IsRational := by
  rintro ⟨w,hw⟩
  obtain ⟨P⟩ := rational_place_source (HpInfiniteArithmetic.p j)
    (by have := HpInfiniteArithmetic.p_gt_one j;linarith) w hw
  exact (HpFamilyNoPoint.family_no_rational_point j).false
    (HasseProjectivePoint.ofHomogeneousPoint _ P)

/-- No rational point on the SAME genuine smooth proper canonical curve
model, obtained from exhaustive actual residue-place charts. -/
theorem family_no_model_point (j : ℕ) :
    ¬ ∃f : Spec (CommRingCat.of ℚ) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=𝟙 _ := by
  rintro ⟨f,hf⟩
  exact family_no_rational_place j
    (CurveRationalPlace07.point_gives_rational_place (HpSchemeModel.model _) f hf)

#print axioms rational_place_source
#print axioms family_no_rational_place
#print axioms family_no_model_point
end
end FourCorner.HpModelNoPoint
