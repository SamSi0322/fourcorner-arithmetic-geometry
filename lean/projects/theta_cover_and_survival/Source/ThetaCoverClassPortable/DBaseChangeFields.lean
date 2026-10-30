import ThetaCoverClassPortable.DBaseChangeGeometry
import Mathlib.Algebra.CharP.Algebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.DRationalInputs
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces
variable {K : Type} [Field K] (t : Spec (.of K) ⟶ Spec (.of ℚ))

/-- Literal pullback of the original OD, without a chosen replacement point. -/
def ODAt : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of K))) (cAt t) :=
  ⟨pullback.lift (t ≫ OD.1) (𝟙 _) (by rw [Category.assoc, OD.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

theorem ODAt_fst : (ODAt t).1 ≫ pullback.fst toBase t = t ≫ OD.1 :=
  pullback.lift_fst _ _ _

include t in
/-- Characteristic zero is derived from the actual map to Spec QQ. -/
theorem charZero_at : CharZero K := by
  obtain ⟨a,_⟩ := Spec.map_surjective t
  letI : Algebra ℚ K := a.hom.toAlgebra
  exact charZero_of_injective_algebraMap (algebraMap ℚ K).injective

local instance : IsIntegral (XAt t) := integral_at t
local instance : IsProper (cAt t) := proper_at t
local instance : SmoothOfRelativeDimension 1 (cAt t) := smooth_at t
local instance : Algebra K (XAt t).functionField := fieldAlgebra (cAt t)

theorem field_isCurveOver_at : IsCurveOver K (XAt t).functionField := by
  letI := charZero_at t
  exact isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one (cAt t)
    (RingEquiv.refl _) (fun _ => rfl)

theorem field_essFiniteType_at : Algebra.EssFiniteType K (XAt t).functionField :=
  essFiniteType_functionField (cAt t)

def originPlaceAt : Place K (XAt t).functionField :=
  (pointEquivRationalPlace (cAt t) (ODAt t)).val

theorem originPlaceAt_degree_one : (originPlaceAt t).deg = 1 :=
  (originPlaceAt t).isRational_iff_deg_eq_one.mp
    (pointEquivRationalPlace (cAt t) (ODAt t)).property

theorem originPlaceAt_stalk_range :
    (algebraMap ((XAt t).presheaf.stalk ((ODAt t).1 (IsLocalRing.closedPoint K)))
      (XAt t).functionField).range = (originPlaceAt t).toValuationSubring.toSubring :=
  pointEquivRationalPlace_range (cAt t) (ODAt t)

/-- Constant-field equality for every actual field extension test, proved
from the actual pulled-back degree-one origin. No closure is assumed. -/
theorem constantsAreBase_at : ConstantsAreBase K (XAt t).functionField := by
  letI := field_isCurveOver_at t
  exact constantsAreBase_of_deg_eq_one (originPlaceAt t) (originPlaceAt_degree_one t)

end FourCorner.DRationalInputs
