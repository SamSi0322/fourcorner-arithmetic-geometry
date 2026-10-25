import QuadraticOrder

noncomputable section
namespace FourCorner.QuadraticOrderEvaluation
open QuadraticOrder
variable {A F E : Type*} [CommRing A] [IsDomain A] [Field F] [Field E]
  [Algebra A F] [IsFractionRing A F] [Algebra F E] [Algebra A E]
  [IsScalarTower A F E]

def evalQuadratic (a : A) (f : A →+* ℚ) (u : ℚ) (hu : u^2 = f a) :
    QuadraticAlgebra A a 0 →+* ℚ := by
  letI : Algebra A ℚ := f.toAlgebra
  refine (QuadraticAlgebra.lift ⟨u,?_⟩).toRingHom
  simp only [Algebra.smul_def,map_zero,zero_mul,mul_one,add_zero]
  change u*u = f a
  simpa only [pow_two] using hu

theorem evalQuadratic_apply (a : A) (f : A →+* ℚ) (u : ℚ) (hu : u^2 = f a)
    (x : QuadraticAlgebra A a 0) :
    evalQuadratic a f u hu x = f x.re + f x.im*u := by
  letI : Algebra A ℚ := f.toAlgebra
  change x.re • (1 : ℚ) + x.im • u = _
  simp only [Algebra.smul_def,mul_one]
  rfl

def evalAdjoin (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) (f : A →+* ℚ) (u : ℚ) (hu : u^2 = f a) :
    Algebra.adjoin A ({z} : Set E) →+* ℚ :=
  (evalQuadratic a f u hu).comp (equivAdjoin a z hz ha).symm.toRingHom

theorem evalAdjoin_algebraMap (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) (f : A →+* ℚ) (u : ℚ) (hu : u^2 = f a) (r : A) :
    evalAdjoin a z hz ha f u hu (algebraMap A (Algebra.adjoin A ({z} : Set E)) r) = f r := by
  change evalQuadratic a f u hu ((equivAdjoin a z hz ha).symm (algebraMap A _ r)) = _
  rw [AlgEquiv.commutes,evalQuadratic_apply]
  simp

theorem equivAdjoin_coe (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) (x : QuadraticAlgebra A a 0) :
    ((equivAdjoin a z hz ha x : Algebra.adjoin A ({z} : Set E)) : E) = toField a z hz x := rfl

/-- The chosen rational root is the value of the actual adjoined generator. -/
theorem evalAdjoin_root (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) (f : A →+* ℚ) (u : ℚ) (hu : u^2 = f a) :
    evalAdjoin a z hz ha f u hu ⟨z,Algebra.subset_adjoin (Set.mem_singleton z)⟩ = u := by
  have he : (⟨z,Algebra.subset_adjoin (Set.mem_singleton z)⟩ : Algebra.adjoin A ({z} : Set E)) =
      equivAdjoin a z hz ha QuadraticAlgebra.omega := by
    apply Subtype.ext
    rw [equivAdjoin_coe,toField_omega]
  rw [he]
  change evalQuadratic a f u hu ((equivAdjoin a z hz ha).symm
    ((equivAdjoin a z hz ha) QuadraticAlgebra.omega)) = u
  rw [AlgEquiv.symm_apply_apply,evalQuadratic_apply]
  simp

end FourCorner.QuadraticOrderEvaluation
#print axioms FourCorner.QuadraticOrderEvaluation.evalAdjoin_algebraMap
#print axioms FourCorner.QuadraticOrderEvaluation.evalAdjoin_root
