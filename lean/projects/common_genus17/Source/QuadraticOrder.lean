import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace FourCorner.QuadraticOrder
variable {A F E : Type*} [CommRing A] [IsDomain A] [Field F] [Field E]
  [Algebra A F] [IsFractionRing A F] [Algebra F E] [Algebra A E]
  [IsScalarTower A F E]

def toField (a : A) (z : E) (hz : z^2 = algebraMap A E a) :
    QuadraticAlgebra A a 0 →ₐ[A] E :=
  QuadraticAlgebra.lift ⟨z,by simpa only [pow_two,Algebra.smul_def,map_zero,zero_mul,mul_one,add_zero] using hz⟩

theorem toField_apply (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (x : QuadraticAlgebra A a 0) :
    toField a z hz x = algebraMap A E x.re + algebraMap A E x.im * z := by
  change x.re • (1 : E) + x.im • z = _
  simp only [Algebra.smul_def,mul_one]

theorem toField_omega (a : A) (z : E) (hz : z^2 = algebraMap A E a) :
    toField a z hz QuadraticAlgebra.omega = z := by
  simp [toField_apply]

theorem base_injective (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [IsScalarTower A F E] : Function.Injective (algebraMap A E) := by
  intro x y h
  apply IsFractionRing.injective A F
  apply (algebraMap F E).injective
  simpa only [← IsScalarTower.algebraMap_apply A F E] using h

theorem toField_eq_zero (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) (x : QuadraticAlgebra A a 0)
    (hx : toField a z hz x = 0) : x = 0 := by
  rw [toField_apply] at hx
  have him : x.im = 0 := by
    by_contra hi
    have hiE : algebraMap A E x.im ≠ 0 := fun h => hi (base_injective (F := F) (h.trans (map_zero _).symm))
    let c : F := -(algebraMap A F x.re) / algebraMap A F x.im
    have hz' : z = -(algebraMap A E x.re) / algebraMap A E x.im := by
      apply (eq_div_iff hiE).mpr
      linear_combination hx
    have hc : algebraMap F E c = z := by
      simp only [c,map_div₀,map_neg,← IsScalarTower.algebraMap_apply A F E]
      exact hz'.symm
    apply ha
    refine ⟨c,?_⟩
    apply (algebraMap F E).injective
    rw [map_mul,← pow_two,hc,hz,← IsScalarTower.algebraMap_apply A F E]
  have hre : x.re = 0 := by
    apply base_injective (F := F) (E := E)
    simpa only [him,map_zero,zero_mul,add_zero] using hx
  apply QuadraticAlgebra.ext
  · simpa only [QuadraticAlgebra.re_zero] using hre
  · simpa only [QuadraticAlgebra.im_zero] using him

theorem toField_injective (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) : Function.Injective (toField a z hz) := by
  intro x y h
  have hh : toField a z hz (x-y) = 0 := by rw [map_sub,h,sub_self]
  exact sub_eq_zero.mp (toField_eq_zero a z hz ha (x-y) hh)

theorem range_eq_adjoin (a : A) (z : E) (hz : z^2 = algebraMap A E a) :
    (toField a z hz).range = Algebra.adjoin A ({z} : Set E) := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    change toField a z hz x ∈ _
    rw [toField_apply]
    exact (Algebra.adjoin A ({z} : Set E)).add_mem
      ((Algebra.adjoin A ({z} : Set E)).algebraMap_mem x.re)
      ((Algebra.adjoin A ({z} : Set E)).mul_mem
        ((Algebra.adjoin A ({z} : Set E)).algebraMap_mem x.im)
        (Algebra.subset_adjoin (Set.mem_singleton z)))
  · apply Algebra.adjoin_le
    intro y hy
    have hyz : y = z := hy
    rw [hyz]
    exact ⟨QuadraticAlgebra.omega,toField_omega a z hz⟩

/-- The integral quadratic order has its genuine universal presentation over
the original valuation ring, using no homomorphism from its fraction field to Q. -/
def equivAdjoin (a : A) (z : E) (hz : z^2 = algebraMap A E a)
    (ha : ¬ IsSquare (algebraMap A F a)) :
    QuadraticAlgebra A a 0 ≃ₐ[A] Algebra.adjoin A ({z} : Set E) :=
  (AlgEquiv.ofInjective (toField a z hz) (toField_injective a z hz ha)).trans
    (Subalgebra.equivOfEq _ _ (range_eq_adjoin a z hz))

end FourCorner.QuadraticOrder
#print axioms FourCorner.QuadraticOrder.toField_injective
#print axioms FourCorner.QuadraticOrder.equivAdjoin
