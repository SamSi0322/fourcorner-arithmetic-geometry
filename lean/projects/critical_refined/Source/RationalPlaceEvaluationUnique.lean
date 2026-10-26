import ResiduePlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

noncomputable section
namespace FourCorner.RationalPlaceEvaluationUnique
open AlgebraicCurve ResiduePlaceEvaluation
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A map of the actual valuation ring to its constant field is surjective
because it fixes the constants. -/
theorem algHom_surjective (v : Place K F) (f : v.toValuationSubring →ₐ[K] K) :
    Function.Surjective f := by
  intro c
  exact ⟨algebraMap K v.toValuationSubring c, f.commutes c⟩

/-- The kernel is the actual maximal ideal, not an assigned fibre label. -/
theorem algHom_kernel (v : Place K F) (f : v.toValuationSubring →ₐ[K] K) :
    RingHom.ker f.toRingHom=IsLocalRing.maximalIdeal v.toValuationSubring :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective f.toRingHom (algHom_surjective v f))

/-- The concrete rational residue evaluation vanishes exactly on the actual
maximal ideal. -/
theorem evaluate_zero_iff_maximal (v : Place K F) (hv : v.IsRational)
    (a : v.toValuationSubring) : evaluate v hv a=0 ↔ a∈IsLocalRing.maximalIdeal v.toValuationSubring := by
  change a∈RingHom.ker (evaluate v hv).toRingHom ↔ _
  rw [algHom_kernel]

/-- There is at most one constant-field algebra evaluation from a valuation
ring. The argument uses its actual maximal ideal. -/
theorem algHom_unique (v : Place K F) (f g : v.toValuationSubring →ₐ[K] K) : f=g := by
  apply AlgHom.ext
  intro x
  have hx : x-algebraMap K v.toValuationSubring (f x)∈RingHom.ker f.toRingHom := by
    change f (x-algebraMap K v.toValuationSubring (f x))=0
    simp only [map_sub,AlgHom.commutes,Algebra.algebraMap_self_apply,sub_self]
  rw [algHom_kernel v f,←algHom_kernel v g] at hx
  change g (x-algebraMap K v.toValuationSubring (f x))=0 at hx
  simp only [map_sub,AlgHom.commutes,Algebra.algebraMap_self_apply,sub_eq_zero] at hx
  exact hx.symm

/-- Existence of a constant-field algebra evaluation proves that the actual
residue field is K; no rationality premise is assumed. -/
theorem isRational_of_algHom (v : Place K F) (f : v.toValuationSubring →ₐ[K] K) :
    v.IsRational := by
  let g : v.ResidueField →ₐ[K] K := Ideal.Quotient.liftₐ _ f (by
    intro x hx
    change x∈RingHom.ker f.toRingHom
    rwa [algHom_kernel v f])
  intro y
  refine ⟨g y,?_⟩
  apply g.injective
  exact g.commutes (g y)

theorem evaluate_eq (v : Place K F) (hv : v.IsRational)
    (f : v.toValuationSubring →ₐ[K] K) : evaluate v hv=f := algHom_unique v _ _

#print axioms algHom_unique
#print axioms isRational_of_algHom
#print axioms evaluate_eq
end FourCorner.RationalPlaceEvaluationUnique
