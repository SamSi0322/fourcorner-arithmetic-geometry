import CommonGenus17Unramified
import CommonFieldCoordinates
import CommonPostFiniteP1
import NormalizedModelPointRestriction

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory IntermediateField
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- The original ordered four-root function field. -/
abbrev baseField (t : K) := CommonLiteralField.field K t
/-- The literal fifth-root field, adjoining Z with Z^2=ell/kappa. -/
abbrev field (t κ : K) := CommonGenus17Field.field K t κ
abbrev fifthRoot (t κ : K) : field t κ := CommonGenus17Unramified.Extension.root K t κ
abbrev fieldInclusion (t κ : K) : baseField t →ₐ[K] field t κ :=
  IsScalarTower.toAlgHom K (baseField t) (field t κ)

theorem fifthRoot_sq (t κ : K) : fifthRoot t κ ^ 2 =
    fieldInclusion t κ (CommonGenus17Field.radicand K t κ) :=
  CommonGenus17Unramified.Extension.root_sq K t κ

def ell (t κ : K) : field t κ := fieldInclusion t κ (CommonLiteralField.ell K t)
def orderedRoot (t κ : K) (i : Fin 4) : field t κ :=
  fieldInclusion t κ (CommonLiteralField.root K t i)

theorem degree_two (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    Module.finrank (baseField t) (field t κ) = 2 :=
  CommonGenus17Field.finrank_eq_two K h0 h1 hm hκ

theorem finite_over_line (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    FiniteDimensional (RatFunc K) (field t κ) := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact FiniteDimensional.trans (RatFunc K) (baseField t) (field t κ)

instance constantsLineTower (t κ : K) : IsScalarTower K (RatFunc K) (field t κ) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  change algebraMap K (field t κ) a = algebraMap (RatFunc K) (field t κ) (algebraMap K (RatFunc K) a)
  rfl


abbrev modelFieldAlgebra (t κ : K) : Algebra K (field t κ) := inferInstance

theorem fifthRoot_sq_literal (t κ : K) : fifthRoot t κ ^ 2 =
    ell t κ / algebraMap K (field t κ) κ := by
  rw [fifthRoot_sq]
  change algebraMap (baseField t) (field t κ) (CommonGenus17Field.radicand K t κ) = _
  simp only [CommonGenus17Field.radicand,CommonLiteralField.ell,ell,fieldInclusion,
    IsScalarTower.toAlgHom_apply,map_div₀,
    ← IsScalarTower.algebraMap_apply K (RatFunc K) (baseField t),
    ← IsScalarTower.algebraMap_apply K (baseField t) (field t κ)]

/-- The actual canonical smooth proper completion of the literal five-root field. -/
def model (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : CurveModel K (field t κ) := by
  letI := finite_over_line t κ h0 h1 hm
  exact SchemeModelFiniteExtension.model K (field t κ)

abbrev curve (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) := (model t κ h0 h1 hm).C
abbrev toBase (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) := (model t κ h0 h1 hm).toBase

theorem model_integral (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : IsIntegral (curve t κ h0 h1 hm) := inferInstance
theorem model_proper (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : IsProper (toBase t κ h0 h1 hm) := inferInstance
theorem model_smooth (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    SmoothOfRelativeDimension 1 (toBase t κ h0 h1 hm) := inferInstance
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.model
#print axioms FourCorner.Genus17Geometry.fifthRoot_sq
#print axioms FourCorner.Genus17Geometry.degree_two

#print axioms FourCorner.Genus17Geometry.fifthRoot_sq_literal
