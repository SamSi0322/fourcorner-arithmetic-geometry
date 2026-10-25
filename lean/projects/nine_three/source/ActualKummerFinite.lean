import FGCardCore
import FGKummerInterface
import OrderedKummer

namespace FourCorner.FGKummer

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]
    {M : Type*} [CommGroup M]

/-- A complete image bound gives finiteness when the rational doubling kernel
has four elements. No independence of the images of these elements is needed. -/
theorem finite_of_image_mem (δ : Multiplicative G →* M)
    (hker : δ.ker = (nsmulAddMonoidHom (α := G) 2).range.toSubgroup)
    (htwo : Nat.card (nsmulAddMonoidHom (α := G) 2).ker = 4)
    (S : Finset M) (hS : ∀ P : G, δ (Multiplicative.ofAdd P) ∈ S)
    (hcard : S.card ≤ 4) : Finite G :=
  FGCardCore.finite_of_double_card htwo
    ((quotient_card_le_of_image_mem δ hker S hS).trans hcard)

open Polynomial WeierstrassCurve.Affine
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    {W : WeierstrassCurve.Affine K} [W.IsCharNeTwoNF] [W.IsElliptic]

/-- The actual number-field Mordell--Weil theorem and the complete ordered
Kummer image together prove that the entire elliptic point group is finite. -/
theorem finite_points_of_ordered_image (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i)))
    (S : Finset (Fin 3 → Units.modPow K 2))
    (hS : ∀ P : W.Point, OrderedSplit.orderedDelta r hr hf (Multiplicative.ofAdd P) ∈ S)
    (hcard : S.card ≤ 4) : Finite W.Point := by
  let : AddGroup.FG W.Point := fg_point_of_numberField
  exact finite_of_image_mem (OrderedSplit.orderedDelta r hr hf)
    (OrderedSplit.orderedDelta_ker r hr hf)
    (two_torsion_card_of_split r hr hf) S hS hcard

/-- Every actual rational point is torsion after a complete four-row ordered
Kummer bound; rank zero is a conclusion, not an input. -/
theorem torsion_points_of_ordered_image (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i)))
    (S : Finset (Fin 3 → Units.modPow K 2))
    (hS : ∀ P : W.Point, OrderedSplit.orderedDelta r hr hf (Multiplicative.ofAdd P) ∈ S)
    (hcard : S.card ≤ 4) (P : W.Point) : IsOfFinAddOrder P := by
  let : Finite W.Point := finite_points_of_ordered_image r hr hf S hS hcard
  exact isOfFinAddOrder_of_finite P

end FourCorner.FGKummer

#print axioms FourCorner.FGKummer.finite_of_image_mem
#print axioms FourCorner.FGKummer.finite_points_of_ordered_image
#print axioms FourCorner.FGKummer.torsion_points_of_ordered_image
