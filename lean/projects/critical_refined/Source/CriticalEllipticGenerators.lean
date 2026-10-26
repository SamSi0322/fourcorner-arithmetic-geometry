import CriticalEllipticField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace FourCorner.CriticalEllipticGenerators
open Polynomial CriticalEllipticField
variable (k : Type*) [Field k]

/-- The two native Weierstrass coordinate functions generate the actual
fraction field. This is a property of the genuine quotient coordinate ring. -/
theorem field_eq_top (S : IntermediateField k (field k))
    (hx : x k∈S) (hy : y k∈S) : S=⊤ := by
  let U:=S.toSubalgebra.comap (IsScalarTower.toAlgHom k (ring k) (field k))
  have hp (p : k[X]) : algebraMap k[X] (ring k) p∈U := by
    change algebraMap (ring k) (field k) (algebraMap k[X] (ring k) p)∈S
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | monomial n z =>
      rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,map_mul,map_pow]
      apply S.mul_mem
      · change algebraMap (ring k) (field k) (algebraMap k[X] (ring k) (algebraMap k k[X] z))∈S
        rw [←IsScalarTower.algebraMap_apply k k[X] (ring k),←IsScalarTower.algebraMap_apply k (ring k) (field k)]
        exact S.algebraMap_mem z
      · exact S.toSubalgebra.pow_mem hx n
  let T : Subalgebra k[X] (ring k) := { U.toSubring with algebraMap_mem' := hp }
  have ht : Algebra.adjoin k[X] {yRing k}≤T := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hy
  dsimp only [yRing] at ht
  rw [AdjoinRoot.adjoinRoot_eq_top] at ht
  have hr (r : ring k) : algebraMap (ring k) (field k) r∈S :=
    ht (show r∈(⊤ : Subalgebra k[X] (ring k)) by trivial)
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (ring k) z
  exact S.div_mem (hr a) (hr b)

end FourCorner.CriticalEllipticGenerators
#print axioms FourCorner.CriticalEllipticGenerators.field_eq_top
