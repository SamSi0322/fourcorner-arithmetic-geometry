import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ThetaCoverClassPortable.ResiduePlaceEvaluation
import Mathlib.AlgebraicGeometry.ResidueField

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.SmoothProperClosedPointPlaces
variable {K : Type u} [Field K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
    [SmoothOfRelativeDimension 1 c] [IsProper c]

abbrev fieldAlgebra : Algebra K X.functionField := (baseToFunctionField c).toAlgebra

/-- The actual place arising from the DVR stalk of a closed point of the
same curve. The arbitrary-field accepted stalk theorem supplies existence. -/
def placeOfClosedPoint (x : closedPoints X) :
    letI := fieldAlgebra c; Place K X.functionField := by
  letI := fieldAlgebra c
  exact Classical.choose (AlgebraicCurve.exists_place_range_stalk_eq c x.val x.property)

theorem range_stalk (x : closedPoints X) :
    letI := fieldAlgebra c
    (algebraMap (X.presheaf.stalk x.val) X.functionField).range=
      (placeOfClosedPoint c x).toValuationSubring.toSubring := by
  letI := fieldAlgebra c
  exact Classical.choose_spec (AlgebraicCurve.exists_place_range_stalk_eq c x.val x.property)

theorem placeOfClosedPoint_injective :
    letI := fieldAlgebra c; Function.Injective (placeOfClosedPoint c) := by
  letI := fieldAlgebra c
  intro x y h
  apply Subtype.ext
  apply AlgebraicCurve.eq_of_range_stalk_eq c
  rw [range_stalk c x,range_stalk c y,h]

theorem placeOfClosedPoint_surjective :
    letI := fieldAlgebra c; Function.Surjective (placeOfClosedPoint c) := by
  letI := fieldAlgebra c
  intro v
  obtain ⟨x,hx,hr⟩ := AlgebraicCurve.exists_closedPoint_range_stalk_eq c v
  refine ⟨⟨x,hx⟩,Place.ext ?_⟩
  apply ValuationSubring.toSubring_injective
  rw [← range_stalk c ⟨x,hx⟩,hr]

/-- All closed points correspond to actual places over ANY field. The later
rational-point restriction does not use the AlgClosed-only pointEquivPlace. -/
def closedPointPlaceEquiv :
    letI := fieldAlgebra c; closedPoints X ≃ Place K X.functionField := by
  letI := fieldAlgebra c
  exact Equiv.ofBijective _ ⟨placeOfClosedPoint_injective c,placeOfClosedPoint_surjective c⟩

@[simp] theorem closedPointPlaceEquiv_apply (x : closedPoints X) :
    letI := fieldAlgebra c; closedPointPlaceEquiv c x=placeOfClosedPoint c x := rfl

/-- Actual local-ring identification inside the fixed function field. -/
def stalkValuationEquiv (x : closedPoints X) :
    letI := fieldAlgebra c
    X.presheaf.stalk x.val ≃+* (placeOfClosedPoint c x).toValuationSubring := by
  letI := fieldAlgebra c
  let g := algebraMap (X.presheaf.stalk x.val) X.functionField
  let f := g.codRestrict (placeOfClosedPoint c x).toValuationSubring.toSubring (fun a => by
    rw [← range_stalk c x]
    exact ⟨a,rfl⟩)
  apply RingEquiv.ofBijective f
  constructor
  · intro a b h
    apply IsFractionRing.injective (X.presheaf.stalk x.val) X.functionField
    exact congrArg Subtype.val h
  · intro y
    have hy : (y : X.functionField)∈g.range := by
      rw [range_stalk c x]
      exact y.property
    obtain ⟨a,ha⟩ := hy
    exact ⟨a,Subtype.ext ha⟩

@[simp] theorem stalkValuationEquiv_coe (x : closedPoints X) (a : X.presheaf.stalk x.val) :
    letI := fieldAlgebra c
    ((stalkValuationEquiv c x a : (placeOfClosedPoint c x).toValuationSubring) : X.functionField)=
      algebraMap (X.presheaf.stalk x.val) X.functionField a := rfl

#print axioms placeOfClosedPoint
#print axioms range_stalk
#print axioms closedPointPlaceEquiv
#print axioms stalkValuationEquiv
end FourCorner.SmoothProperClosedPointPlaces
