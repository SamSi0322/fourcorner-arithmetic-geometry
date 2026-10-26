import HpCanonicalNetPreservation
import HpMonomialRigidity

namespace FourCorner.HpActualMonomial
open AlgebraicCurve HpLiteralField HpFieldGeometry HpCanonicalForms HpCanonicalBasis HpCanonicalIsomorphism
  HpCanonicalActionFormula HpQuadraticRelations HpDiagonalNet HpQuadraticExpansion HpDiagonalKernelRigidity
noncomputable section
attribute [local instance] Classical.propDecidable
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
local instance perfect : PerfectField K := IsAlgClosed.perfectField K
local instance finite (p : K) : FiniteDimensional (RatFunc K) (field K p) := finite_over_line K p
local instance curve (p : K) : IsCurveOver K (field K p) := isCurveOver K p
local instance finiteType (p : K) : Algebra.EssFiniteType K (field K p) := RatFuncFiniteExtension.essFiniteType K (field K p)
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule
variable {p q : K} (e : field K p ≃ₐ[K] field K q)
  (hp : p ≠ 0) (hpa : p-1 ≠ 0) (hpb : p+1 ≠ 0)
  (hq : q ≠ 0) (hqa : q-1 ≠ 0) (hqb : q+1 ≠ 0)

theorem actual_monomial :
    ∃σ : Equiv.Perm (Fin 5),∃a : Fin 5 → K,(∀i,a i ≠ 0) ∧ ∀i,
      linearCoordinate K e hp hpa hpb hq hqa hqb i=
        algebraMap K (field K q) (a i)*coordinate K q (σ i) := by
  obtain ⟨σ,c,hc,hcol,hfun⟩ := HpMonomialRigidity.monomial_of_axes
    (transposeEquiv K (coordinateAction K e hp hpa hpb hq hqa hqb))
    (HpCanonicalNetPreservation.actual_inverse_axis K e hp hpa hpb hq hqa hqb)
  refine ⟨σ,fun i => (c i)⁻¹,fun i => inv_ne_zero (hc i),?_⟩
  have hm (i j : Fin 5) : matrix K e hp hpa hpb hq hqa hqb j i=
      if j=σ i then (c i)⁻¹ else 0 := by
    have h := hfun (Pi.single j 1) i
    rw [transposeEquiv_apply] at h
    simpa [matrix,Pi.single_apply,div_eq_mul_inv,eq_comm] using h
  intro i
  simp [linearCoordinate,hm,apply_ite]

theorem coordinate_sq_direct (r : K) (i : Fin 5) :
    coordinate K r i^2=algebraMap K (field K r) (slope K r i)*
      algebraMap (RatFunc K) (field K r) RatFunc.X+algebraMap K (field K r) (intercept K r i) := by
  rw [coordinate_sq,map_add,map_mul]
  rfl

theorem linear_rho_eq_zero (r a b : K) :
    algebraMap K (field K r) a*algebraMap (RatFunc K) (field K r) RatFunc.X+
      algebraMap K (field K r) b=0 ↔ a=0 ∧ b=0 := by
  have he : algebraMap K (field K r) a*algebraMap (RatFunc K) (field K r) RatFunc.X+
      algebraMap K (field K r) b=
      algebraMap (RatFunc K) (field K r) (algebraMap K (RatFunc K) a*RatFunc.X+algebraMap K (RatFunc K) b) := by
    rw [map_add,map_mul]
    rfl
  rw [he,map_eq_zero,linear_rational_eq_zero]

#print axioms actual_monomial
#print axioms coordinate_sq_direct
#print axioms linear_rho_eq_zero
end
end FourCorner.HpActualMonomial
