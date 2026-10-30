import Genus17Model
import QuadraticDiscriminant

noncomputable section
namespace FourCorner.Genus17PowerBasis
open Genus17Geometry IntermediateField
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual power basis of the literal simple fifth-root field. -/
def basis (t κ : K) : PowerBasis (baseField t) (field t κ) :=
  IntermediateField.adjoin.powerBasis (CommonGenus17Unramified.Extension.radical_integral K t κ)

theorem gen_eq (t κ : K) : (basis t κ).gen = fifthRoot t κ := rfl

theorem dim_eq_two (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    (basis t κ).dim = 2 := by
  rw [← (basis t κ).finrank]
  exact degree_two t κ h0 h1 hm hκ

theorem discr_eq (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    Algebra.discr (baseField t) (basis t κ).basis =
      4 * CommonGenus17Field.radicand K t κ := by
  apply QuadraticDiscriminant.discr_eq (basis t κ) (dim_eq_two t κ h0 h1 hm hκ)
  · exact CommonGenus17Field.radicand_nonsquare K h0 h1 hm hκ
  · rw [gen_eq]
    exact fifthRoot_sq t κ

end FourCorner.Genus17PowerBasis
#print axioms FourCorner.Genus17PowerBasis.gen_eq
#print axioms FourCorner.Genus17PowerBasis.dim_eq_two
#print axioms FourCorner.Genus17PowerBasis.discr_eq
