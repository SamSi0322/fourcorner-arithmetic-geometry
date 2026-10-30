import RadicalLinearization
import OddFiveRamification

noncomputable section
namespace FourCorner.LinearizedFactors
open RadicalLinearization AlgebraicCurve
variable {k : Type*} [Field k]
def branch (t : k) : Fin 5 → k
  | 0 => -(t+1)
  | 1 => t-1
  | 2 => t+1
  | 3 => -(t-1)
  | 4 => 0
def coefficient (t κ : k) : Fin 5 → k
  | 0 => 1
  | 1 => 1
  | 2 => -(t-1)*κ⁻¹
  | 3 => (t+1)*κ⁻¹
  | 4 => κ⁻¹
theorem values_factor (t κ a : k) (i : Fin 5) :
    values t κ⁻¹ a i = coefficient t κ i * (a-branch t i) := by
  fin_cases i <;> simp only [values,coefficient,branch] <;> ring

theorem coefficient_ne_zero {t κ : k} (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (i : Fin 5) : coefficient t κ i ≠ 0 := by
  have hs : t-1≠0 := sub_ne_zero.mpr h1
  have hT : t+1≠0 := by intro h; apply hm; linear_combination h
  fin_cases i <;> simp only [coefficient]; all_goals first | exact one_ne_zero | exact inv_ne_zero hκ | exact mul_ne_zero (neg_ne_zero.mpr hs) (inv_ne_zero hκ) | exact mul_ne_zero hT (inv_ne_zero hκ)

theorem values_zero_iff {t κ : k} (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (a : k) (i : Fin 5) : values t κ⁻¹ a i=0 ↔ a=branch t i := by
  rw [values_factor,mul_eq_zero]
  simp only [coefficient_ne_zero h1 hm hκ i,false_or,sub_eq_zero]

theorem roots_sq_factor (t κ : k) (hκ : κ≠0) (i : Fin 5) :
    roots k t κ i ^2 = algebraMap k (CommonGenus17Field.field k t κ) (coefficient t κ i) *
      algebraMap (RatFunc k) (CommonGenus17Field.field k t κ) (OddFourPlaces.linear (branch t i)) := by
  rw [roots_sq k t κ hκ i,OddFourPlaces.linear_eq,map_sub]
  rw [←IsScalarTower.algebraMap_apply k (RatFunc k) (CommonGenus17Field.field k t κ)]
  fin_cases i <;> simp only [values,coefficient,branch,map_mul,map_neg,map_sub,map_add,map_one,map_inv₀,map_zero]
  all_goals dsimp only [RadicalLinearization.ell]; ring

theorem roots_ne_zero {t κ : k} (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (i : Fin 5) : roots k t κ i ≠ 0 := by
  have h := mul_ne_zero ((map_ne_zero (algebraMap k (CommonGenus17Field.field k t κ))).mpr (coefficient_ne_zero h1 hm hκ i))
    ((map_ne_zero (algebraMap (RatFunc k) (CommonGenus17Field.field k t κ))).mpr (OddFourPlaces.linear_ne_zero (branch t i)))
  rw [←roots_sq_factor t κ hκ i] at h
  intro hz
  exact h (by rw [hz,zero_pow (by decide : 2≠0)])
end FourCorner.LinearizedFactors
#print axioms FourCorner.LinearizedFactors.roots_ne_zero
#print axioms FourCorner.LinearizedFactors.roots_sq_factor
