import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.PolynomialChartRank
open Polynomial IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The specified polynomial action on the ACTUAL simple intermediate field. -/
@[instance_reducible] def simpleAlgebra (f : F) : Algebra K[X] K⟮f⟯ :=
  (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K f)).toRingHom.toAlgebra

theorem simpleAlgebra_coe (f : F) (p : K[X]) :
    letI := simpleAlgebra (K:=K) f
    ((algebraMap K[X] K⟮f⟯ p : K⟮f⟯) : F)=Polynomial.aeval f p := by
  exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply K f p

theorem simple_isFractionRing (f : F) (ht : Transcendental K f) :
    letI := simpleAlgebra (K:=K) f
    IsFractionRing K[X] K⟮f⟯ := by
  letI := simpleAlgebra (K:=K) f
  have hinj : Function.Injective (algebraMap K[X] K⟮f⟯) := by
    intro p q h
    apply transcendental_iff_injective.mp ht
    have hh := congrArg (fun z : K⟮f⟯ => (z : F)) h
    simpa only [simpleAlgebra_coe] using hh
  letI : FaithfulSMul K[X] K⟮f⟯ := (faithfulSMul_iff_algebraMap_injective K[X] K⟮f⟯).mpr hinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K (x := (z:F))).mp z.property
  refine ⟨p,q,?_⟩
  apply Subtype.ext
  simpa only [IntermediateField.coe_div,simpleAlgebra_coe] using hpq

/-- A genuine fraction-ring presentation of an actual chart compares its
EXACT aeval-polynomial rank to the degree of the SAME native field over K(f).
No finite-free or curve conclusion is postulated by this rank identity. -/
theorem polynomial_rank_eq_field_degree {A : Type*} [CommRing A] [Algebra K A]
    (a : A) (g : A →ₐ[K] F) (ht : Transcendental K (g a))
    (hfrac : letI := g.toRingHom.toAlgebra; IsFractionRing A F) :
    letI := (Polynomial.aeval (R:=K) a).toRingHom.toAlgebra
    Module.finrank K[X] A=Module.finrank K⟮g a⟯ F := by
  letI := (Polynomial.aeval (R:=K) a).toRingHom.toAlgebra
  letI := g.toRingHom.toAlgebra
  letI : Algebra K[X] F := (Polynomial.aeval (R:=K) (g a)).toRingHom.toAlgebra
  letI : IsScalarTower K[X] A F := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    change Polynomial.aeval (R:=K) (g a) p=g (Polynomial.aeval (R:=K) a p)
    exact Polynomial.aeval_algHom_apply g a p
  letI := simpleAlgebra (K:=K) (g a)
  letI := simple_isFractionRing (K:=K) (g a) ht
  letI : IsScalarTower K[X] K⟮g a⟯ F := by
    apply IsScalarTower.of_algebraMap_eq
    intro p
    exact (simpleAlgebra_coe (K:=K) (g a) p).symm
  letI := hfrac
  exact (IsFractionRing.finrank_eq K[X] K⟮g a⟯ A F).symm

#print axioms simple_isFractionRing
#print axioms polynomial_rank_eq_field_degree
end FourCorner.PolynomialChartRank
