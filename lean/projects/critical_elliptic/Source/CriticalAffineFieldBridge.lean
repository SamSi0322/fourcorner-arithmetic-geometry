import CriticalAffineGeometry
import CriticalFieldCoordinates
import FractionFieldGenerators

noncomputable section
namespace FourCorner.CriticalAffineFieldBridge
open CriticalAffineGeometry
variable {k : Type*} [Field k] (i : k) [IsDomain (ring i)]

/-- The actual fraction field of the literal V0 affine quotient. -/
abbrev field := FractionRing (ring i)
def coordinate (j : Fin 3) : field i := algebraMap (ring i) (field i) (CriticalAffineGeometry.coordinate i j)

theorem equations : coordinate i 1^2-1=algebraMap k (field i) i*(coordinate i 0^2-1) ∧
    coordinate i 2^2-1=(1+algebraMap k (field i) i)*(coordinate i 0^2-1) := by
  have h := CriticalAffineGeometry.coordinate_equations i
  constructor
  · simpa only [coordinate,map_sub,map_pow,map_mul,map_one,
      ←IsScalarTower.algebraMap_apply k (ring i) (field i)] using
      congrArg (algebraMap (ring i) (field i)) h.1
  · simpa only [coordinate,map_sub,map_pow,map_mul,map_one,map_add,
      ←IsScalarTower.algebraMap_apply k (ring i) (field i)] using
      congrArg (algebraMap (ring i) (field i)) h.2

theorem generates : IntermediateField.adjoin k (Set.range ![coordinate i 0,coordinate i 1,coordinate i 2])=⊤ := by
  have he : (fun j => algebraMap (ring i) (field i) (CriticalAffineGeometry.coordinate i j)) =
      ![coordinate i 0,coordinate i 1,coordinate i 2] := by
    funext j
    fin_cases j <;> rfl
  rw [←he]
  exact FractionFieldGenerators.adjoin_eq_top _ (CriticalAffineGeometry.coordinate_generates i)

/-- Concrete actual affine-field bridge. The outstanding domain and
transcendence inputs are native affine facts supplied by the geometry line;
no genus, isomorphism or projective-model comparison is an input. -/
def equiv (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (ha : Transcendental k (coordinate i 0)) :
    CriticalEllipticField.field k ≃ₐ[k] field i :=
  CriticalFieldEquivalence.equiv i hi h2 (coordinate i 0) (coordinate i 1) (coordinate i 2)
    (equations i).1 (equations i).2 ha (generates i)

theorem original_coordinates (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (ha : Transcendental k (coordinate i 0)) :
    CriticalDirectMap.inverseA (algebraMap k (field i) i)
      (equiv i hi h2 ha (CriticalEllipticField.x k)) (equiv i hi h2 ha (CriticalEllipticField.y k))=coordinate i 0 ∧
    CriticalDirectMap.inverseB (algebraMap k (field i) i)
      (equiv i hi h2 ha (CriticalEllipticField.x k)) (equiv i hi h2 ha (CriticalEllipticField.y k))=coordinate i 1 ∧
    CriticalDirectMap.inverseC (algebraMap k (field i) i)
      (equiv i hi h2 ha (CriticalEllipticField.x k)) (equiv i hi h2 ha (CriticalEllipticField.y k))=coordinate i 2 :=
  CriticalFieldEquivalence.original_coordinates i hi h2 _ _ _ (equations i).1 (equations i).2 ha (generates i)

end FourCorner.CriticalAffineFieldBridge
#print axioms FourCorner.CriticalAffineFieldBridge.generates
#print axioms FourCorner.CriticalAffineFieldBridge.equiv
#print axioms FourCorner.CriticalAffineFieldBridge.original_coordinates
