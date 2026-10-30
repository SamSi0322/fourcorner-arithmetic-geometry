import InfinityRootOrders

noncomputable section
namespace FourCorner.InfinityChartEquations
open RadicalLinearization InfinityRootOrders
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ

def values {R : Type*} [CommRing R] (t κ ki u : R) : Fin 4 → R
  | 0 => κ+(t+1)*u^2
  | 1 => κ-(t-1)*u^2
  | 2 => (t-1)*(t+1)*ki*u^2-(t-1)
  | 3 => (t+1)+(t+1)*(t-1)*ki*u^2

theorem map_values {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t κ ki u : R) (i : Fin 4) :
    f (values t κ ki u i)=values (f t) (f κ) (f ki) (f u) i := by
  fin_cases i <;> simp only [values,map_add,map_sub,map_mul,map_one,map_pow]

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem normalized_sq (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0) (i : Fin 4) :
    normalized t κ i ^2 = values (algebraMap k E t) (algebraMap k E κ)
      (algebraMap k E κ⁻¹) (parameter t κ) i := by
  have hz := LinearizedFactors.roots_ne_zero h1 hm hκ 4
  have hk : algebraMap k E κ≠0 := (map_ne_zero _).mpr hκ
  have h4 := roots_sq k t κ hκ 4
  change roots k t κ 4^2=RadicalLinearization.ell k t κ * algebraMap k E κ⁻¹ at h4
  rw [map_inv₀] at h4
  have he : RadicalLinearization.ell k t κ=algebraMap k E κ * roots k t κ 4^2 := by
    field_simp [hk] at h4
    linear_combination -h4
  have hr := roots_sq k t κ hκ i.castSucc
  rw [normalized,div_pow,hr]
  fin_cases i <;> simp only [RadicalLinearization.values,Fin.castSucc_mk,values,parameter]
  all_goals rw [he]
  all_goals try simp only [map_inv₀]
  all_goals field_simp [hz,hk] <;> ring
end FourCorner.InfinityChartEquations
#print axioms FourCorner.InfinityChartEquations.normalized_sq
