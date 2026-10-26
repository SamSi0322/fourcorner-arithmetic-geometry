import HpActualMonomial

namespace FourCorner.HpBranchLinearDescent
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

open HpActualMonomial
open scoped Matrix

theorem square_coefficients (σ : Equiv.Perm (Fin 5)) (a : Fin 5 → K) (h : field K q)
    (hs : ∀i,e (coordinate K p i)*h=algebraMap K (field K q) (a i)*coordinate K q (σ i)) :
    ∀i,(algebraMap K (field K q) (slope K p i)*e (algebraMap (RatFunc K) (field K p) RatFunc.X)+
      algebraMap K (field K q) (intercept K p i))*h^2=
      algebraMap K (field K q) (a i^2)*(algebraMap K (field K q) (slope K q (σ i))*
        algebraMap (RatFunc K) (field K q) RatFunc.X+algebraMap K (field K q) (intercept K q (σ i))) := by
  intro i
  have hh := congrArg (fun z : field K q => z^2) (hs i)
  simp only [mul_pow,← map_pow] at hh
  rw [coordinate_sq_direct,map_add,map_mul,AlgEquiv.commutes,AlgEquiv.commutes,
    coordinate_sq_direct] at hh
  exact hh

theorem coefficient_identities (σ : Equiv.Perm (Fin 5)) (a : Fin 5 → K) (h : field K q)
    (hs : ∀i,e (coordinate K p i)*h=algebraMap K (field K q) (a i)*coordinate K q (σ i)) (i : Fin 5) :
    (slope K p i*(a 0^2*slope K q (σ 0))+intercept K p i*(p*a 4^2*slope K q (σ 4))=
      p*a i^2*slope K q (σ i)) ∧
    (slope K p i*(a 0^2*intercept K q (σ 0))+intercept K p i*(p*a 4^2*intercept K q (σ 4))=
      p*a i^2*intercept K q (σ i)) := by
  let f := algebraMap K (field K q)
  have hi := square_coefficients K e σ a h hs i
  have h0 := square_coefficients K e σ a h hs 0
  have h4 := square_coefficients K e σ a h hs 4
  have hs0 : slope K p 0=p := rfl
  have hb0 : intercept K p 0=0 := rfl
  have hs4 : slope K p 4=0 := rfl
  have hb4 : intercept K p 4=1 := rfl
  simp only [hs0,hb0,hs4,hb4,map_zero,map_one,zero_mul,mul_zero,add_zero,zero_add,one_mul] at h0 h4
  simp only [map_pow] at hi h0 h4
  have hr := (linear_rho_eq_zero K q
    (slope K p i*(a 0^2*slope K q (σ 0))+intercept K p i*(p*a 4^2*slope K q (σ 4))-
      p*a i^2*slope K q (σ i))
    (slope K p i*(a 0^2*intercept K q (σ 0))+intercept K p i*(p*a 4^2*intercept K q (σ 4))-
      p*a i^2*intercept K q (σ i))).mp (by
        simp only [map_sub,map_add,map_mul,map_pow]
        linear_combination f p*hi-f (slope K p i)*h0-f p*f (intercept K p i)*h4)
  exact ⟨sub_eq_zero.mp hr.1,sub_eq_zero.mp hr.2⟩

include e hp hpa hpb hq hqa hqb in
/-- The actual isomorphism descends to an invertible two-dimensional
linear transformation, with the five literal branch covectors permuted. -/
theorem actual_branch_matrix :
    ∃σ : Equiv.Perm (Fin 5),∃B : Matrix (Fin 2) (Fin 2) K,∃b : Fin 5 → K,
      B.det ≠ 0 ∧ (∀i,b i ≠ 0) ∧ ∀i,
      (slope K p i*B 0 0+intercept K p i*B 1 0=b i*slope K q (σ i)) ∧
      (slope K p i*B 0 1+intercept K p i*B 1 1=b i*intercept K q (σ i)) := by
  obtain ⟨σ,a,ha,hm⟩ := actual_monomial K e hp hpa hpb hq hqa hqb
  let h := linearCoordinate K e hp hpa hpb hq hqa hqb 4
  have hs (i : Fin 5) : e (coordinate K p i)*h=algebraMap K (field K q) (a i)*coordinate K q (σ i) :=
    (coordinate_scaling K e hp hpa hpb hq hqa hqb i).trans (hm i)
  let B : Matrix (Fin 2) (Fin 2) K :=
    !![a 0^2*slope K q (σ 0),a 0^2*intercept K q (σ 0);
      p*a 4^2*slope K q (σ 4),p*a 4^2*intercept K q (σ 4)]
  refine ⟨σ,B,fun i => p*a i^2,?_,fun i => mul_ne_zero hp (pow_ne_zero _ (ha i)),?_⟩
  · have hd : B.det=(a 0^2*p*a 4^2)*HpAxisQuadrics.determinant K q (σ 0) (σ 4) := by
      simp [B,Matrix.det_fin_two,HpAxisQuadrics.determinant]
      ring
    rw [hd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ha 0)) hp) (pow_ne_zero _ (ha 4)))
      (HpAxisQuadrics.determinant_ne_zero K q hq hqa hqb _ _ (σ.injective.ne (by decide)))
  · intro i
    exact coefficient_identities K e σ a h hs i

#print axioms square_coefficients
#print axioms coefficient_identities
#print axioms actual_branch_matrix
end
end FourCorner.HpBranchLinearDescent
