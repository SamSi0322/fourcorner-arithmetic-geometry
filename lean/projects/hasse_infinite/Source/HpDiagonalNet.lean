import HpQuadraticRelations

namespace FourCorner.HpDiagonalNet
open HpQuadraticRelations
noncomputable section
variable (K : Type*) [Field K]
attribute [local instance] Classical.propDecidable

def functional (v : Fin 5 → K) : (Fin 5 → K) →ₗ[K] K where
  toFun d := ∑i,d i*v i
  map_add' d e := by simp [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c d := by simp [Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]

def coefficientMap (p : K) : (Fin 5 → K) →ₗ[K] K × K :=
  (functional K (slope K p)).prod (functional K (intercept K p))

def net (p : K) : Submodule K (Fin 5 → K) := (coefficientMap K p).ker

theorem mem_net (p : K) (d : Fin 5 → K) : d∈net K p ↔ slopeSum K p d=0 ∧ interceptSum K p d=0 := by
  simp [net,coefficientMap,functional,slopeSum,interceptSum,Prod.ext_iff]

theorem coefficientMap_surjective (p : K) (hp : p ≠ 0) : Function.Surjective (coefficientMap K p) := by
  rintro ⟨a,b⟩
  refine ⟨![a/p,0,0,0,b],?_⟩
  ext <;> simp [coefficientMap,functional,slope,intercept,Fin.sum_univ_succ,div_mul_cancel₀ a hp]

theorem net_finrank (p : K) (hp : p ≠ 0) : Module.finrank K (net K p)=3 := by
  have h := (coefficientMap K p).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (coefficientMap_surjective K p hp),finrank_top] at h
  simp only [Module.finrank_prod,Module.finrank_self,Module.finrank_pi_fintype,Fintype.card_fin,
    Finset.sum_const,smul_eq_mul,mul_one,Finset.card_univ] at h
  change Module.finrank K (LinearMap.ker (coefficientMap K p))=3
  omega

#print axioms net_finrank
end
end FourCorner.HpDiagonalNet
