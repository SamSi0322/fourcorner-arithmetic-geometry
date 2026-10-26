import HpDifferentialTransport
import HpQuadraticRelations

namespace FourCorner.HpCanonicalIsomorphism
open AlgebraicCurve HpLiteralField HpFieldGeometry HpCanonicalForms HpCanonicalBasis
noncomputable section
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
attribute [local instance] Classical.propDecidable
local instance perfect : PerfectField K := IsAlgClosed.perfectField K
local instance finite (p : K) : FiniteDimensional (RatFunc K) (field K p) := finite_over_line K p
local instance curve (p : K) : IsCurveOver K (field K p) := isCurveOver K p
local instance finiteType (p : K) : Algebra.EssFiniteType K (field K p) := RatFuncFiniteExtension.essFiniteType K (field K p)
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule
local instance coords (p : K) : ∀v : Place K (field K p),v.DCoordGenerates := dCoordGenerates_of_isCurveOver

def regularMap {p q : K} (e : field K p ≃ₐ[K] field K q) :
    regularDifferentials K (field K p) →ₗ[K] regularDifferentials K (field K q) :=
  ((pullbackDiff e.toAlgHom).comp (regularDifferentials K (field K p)).subtype).codRestrict
    (regularDifferentials K (field K q)) (fun ω => HpDifferentialTransport.pullback_regular e ω.property)

theorem regularMap_injective {p q : K} (e : field K p ≃ₐ[K] field K q)
    (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0) : Function.Injective (regularMap K e) := by
  intro a b hab
  apply Subtype.ext
  obtain ⟨w,_⟩ := infinity_place_exists K q hq hqa hqb
  exact HpDifferentialTransport.pullback_injective e w (congrArg Subtype.val hab)

def regularEquiv {p q : K} (e : field K p ≃ₐ[K] field K q)
    (hp : p ≠ 0) (hpa : p-1 ≠ 0) (hpb : p+1 ≠ 0)
    (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0) :
    regularDifferentials K (field K p) ≃ₗ[K] regularDifferentials K (field K q) := by
  letI := (regular_space_dimension K p hp hpa hpb).1
  letI := (regular_space_dimension K q hq hqa hqb).1
  exact (regularMap K e).linearEquivOfInjective (regularMap_injective K e hq hqa hqb)
    ((regular_space_dimension K p hp hpa hpb).2.trans (regular_space_dimension K q hq hqa hqb).2.symm)

/-- An actual field isomorphism gives an invertible linear action on the five
canonical coordinates, via the intrinsic regular-differential basis. -/
def coordinateAction {p q : K} (e : field K p ≃ₐ[K] field K q)
    (hp : p ≠ 0) (hpa : p-1 ≠ 0) (hpb : p+1 ≠ 0)
    (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0) :
    (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
  ((HpCanonicalBasis.basis K p hp hpa hpb).equivFun.symm.trans
    (regularEquiv K e hp hpa hpb hq hqa hqb)).trans
      (HpCanonicalBasis.basis K q hq hqa hqb).equivFun

#print axioms regularMap
#print axioms regularMap_injective
#print axioms regularEquiv
#print axioms coordinateAction
end
end FourCorner.HpCanonicalIsomorphism
