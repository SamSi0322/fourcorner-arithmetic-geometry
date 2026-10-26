import SmoothProperRationalPointPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.SmoothProperPointPlaceTransport
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces
variable {K F G : Type u} [Field K] [Field F] [Field G] [Algebra K F] [Algebra K G]

theorem isRational_congr (e : F ≃ₐ[K] G) (v : Place K F) :
    (Place.congrEquiv e.toRingEquiv e.commutes v).IsRational ↔ v.IsRational := by
  let q := Place.congrResidueAlgEquiv e.toRingEquiv e.commutes v
  constructor
  · intro h y
    obtain ⟨a,ha⟩ := h (q y)
    refine ⟨a,q.injective ?_⟩
    rw [q.commutes]
    exact ha
  · intro h y
    obtain ⟨a,ha⟩ := h (q.symm y)
    refine ⟨a,?_⟩
    exact (q.commutes a).symm.trans ((congrArg q ha).trans (q.apply_symm_apply y))

/-- Rational places are transported through the GIVEN K-algebra field
isomorphism, retaining the original constant-field embedding. -/
def rationalPlaceCongr (e : F ≃ₐ[K] G) :
    {v : Place K F // v.IsRational} ≃ {v : Place K G // v.IsRational} := by
  let q := Place.congrEquiv e.toRingEquiv e.commutes
  refine
    { toFun := fun v => ⟨q v.val,(isRational_congr e v.val).mpr v.property⟩
      invFun := fun w => ⟨q.symm w.val,(isRational_congr e (q.symm w.val)).mp (by
        change (q (q.symm w.val)).IsRational
        rw [q.apply_symm_apply]
        exact w.property)⟩
      left_inv := by intro v;apply Subtype.ext;exact q.symm_apply_apply v.val
      right_inv := by intro w;apply Subtype.ext;exact q.apply_symm_apply w.val }

variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]
  [SmoothOfRelativeDimension 1 c] [IsProper c]

/-- The SAME curve's K-points correspond to rational places in a GIVEN
K-isomorphic presentation of its function field. This uses the supplied
base-preserving map, not a newly chosen field or curve model. -/
def pointEquivRationalPlace_of_fieldEquiv
    (e : letI := fieldAlgebra c; F ≃ₐ[K] X.functionField) :
    RationalPoint c ≃ {v : Place K F // v.IsRational} := by
  letI := fieldAlgebra c
  exact (pointEquivRationalPlace c).trans (rationalPlaceCongr e).symm

theorem natCard_points_eq_rationalPlaces_of_fieldEquiv
    (e : letI := fieldAlgebra c; F ≃ₐ[K] X.functionField) :
    Nat.card (RationalPoint c)=Nat.card {v : Place K F // v.IsRational} :=
  Nat.card_congr (pointEquivRationalPlace_of_fieldEquiv c e)

#print axioms isRational_congr
#print axioms rationalPlaceCongr
#print axioms pointEquivRationalPlace_of_fieldEquiv
#print axioms natCard_points_eq_rationalPlaces_of_fieldEquiv
end FourCorner.SmoothProperPointPlaceTransport
